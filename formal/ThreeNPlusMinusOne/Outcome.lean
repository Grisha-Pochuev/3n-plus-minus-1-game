import ThreeNPlusMinusOne.NormalForm
import ThreeNPlusMinusOne.Certificate

set_option autoImplicit false

/-!
# Finite outcomes and the exact no-DRAW bridge

The height-indexed predicates below are finite strategy trees.  Heights are
indices, rather than functions obtained by eliminating a proposition into
data; this keeps the development within Lean's proof-irrelevance rules.
-/

namespace ThreeNPlusMinusOne

mutual
  /-- A finite winning strategy tree of exact height `height`. -/
  inductive WinningTree : Nat → Nat → Prop
    | moveA {q height : Nat} (nonterminal : 0 < q)
        (reply : LosingTree (A q) height) : WinningTree q (height + 1)
    | moveB {q height : Nat} (nonterminal : 0 < q)
        (reply : LosingTree (B q) height) : WinningTree q (height + 1)

  /-- A finite losing strategy tree of exact height `height`. -/
  inductive LosingTree : Nat → Nat → Prop
    | terminal : LosingTree 0 0
    | replies {q heightA heightB : Nat} (nonterminal : 0 < q)
        (replyA : WinningTree (A q) heightA)
        (replyB : WinningTree (B q) heightB) :
        LosingTree q (max heightA heightB + 1)
end

def Winning (q : Nat) : Prop :=
  ∃ height, WinningTree q height

def Losing (q : Nat) : Prop :=
  ∃ height, LosingTree q height

/-- A state reached in two moves through either first child. -/
def CommonGrandchild (grandchild ancestor : Nat) : Prop :=
  (grandchild = A (A ancestor) ∨ grandchild = B (A ancestor)) ∧
    (grandchild = A (B ancestor) ∨ grandchild = B (B ancestor))

namespace LosingTree

/-- Every positive legal child carried by a losing proof tree has a winning
proof tree at least one level lower. -/
theorem positive_child_lower
    {q height child : Nat} (tree : LosingTree q height)
    (childPositive : 0 < child)
    (move : child = A q ∨ child = B q) :
    ∃ childHeight,
      WinningTree child childHeight ∧ childHeight + 1 ≤ height := by
  cases tree with
  | terminal =>
      rcases move with move | move <;> simp [A, B] at move <;> omega
  | replies nonterminal replyA replyB =>
      rcases move with moveA | moveB
      · subst child
        exact ⟨_, replyA, by omega⟩
      · subst child
        exact ⟨_, replyB, by omega⟩

end LosingTree

namespace WinningTree

/-- A positive common grandchild of both legal branches lowers every
concrete winning proof height by at least two. -/
theorem commonGrandchild_lower
    {ancestor grandchild height : Nat}
    (tree : WinningTree ancestor height)
    (grandchildPositive : 0 < grandchild)
    (common : CommonGrandchild grandchild ancestor) :
    ∃ grandchildHeight,
      WinningTree grandchild grandchildHeight ∧
        grandchildHeight + 2 ≤ height := by
  cases tree with
  | moveA nonterminal reply =>
      obtain ⟨grandchildHeight, grandchildTree, lower⟩ :=
        reply.positive_child_lower grandchildPositive common.1
      exact ⟨grandchildHeight, grandchildTree, by omega⟩
  | moveB nonterminal reply =>
      obtain ⟨grandchildHeight, grandchildTree, lower⟩ :=
        reply.positive_child_lower grandchildPositive common.2
      exact ⟨grandchildHeight, grandchildTree, by omega⟩

end WinningTree

namespace Winning

theorem moveA {q : Nat} (nonterminal : 0 < q) (reply : Losing (A q)) :
    Winning q := by
  obtain ⟨height, tree⟩ := reply
  exact ⟨height + 1, WinningTree.moveA nonterminal tree⟩

theorem moveB {q : Nat} (nonterminal : 0 < q) (reply : Losing (B q)) :
    Winning q := by
  obtain ⟨height, tree⟩ := reply
  exact ⟨height + 1, WinningTree.moveB nonterminal tree⟩

end Winning

namespace Losing

theorem terminal : Losing 0 :=
  ⟨0, LosingTree.terminal⟩

theorem replies {q : Nat} (nonterminal : 0 < q)
    (replyA : Winning (A q)) (replyB : Winning (B q)) : Losing q := by
  obtain ⟨heightA, treeA⟩ := replyA
  obtain ⟨heightB, treeB⟩ := replyB
  exact ⟨max heightA heightB + 1,
    LosingTree.replies nonterminal treeA treeB⟩

end Losing

/-- An unresolved state: neither player has a finite winning proof tree. -/
def Draw (q : Nat) : Prop :=
  ¬ Winning q ∧ ¬ Losing q

/-- A state is resolved when one of the two finite outcome trees exists. -/
def Resolved (q : Nat) : Prop :=
  Winning q ∨ Losing q

/-- Exact two-edge move relation in the conjugated game. -/
def ConjugatedMove (next current : Nat) : Prop :=
  0 < current ∧ (next = A current ∨ next = B current)

theorem terminal_losing : Losing 0 :=
  Losing.terminal

theorem terminal_not_draw : ¬ Draw 0 := by
  intro hdraw
  exact hdraw.2 terminal_losing

theorem Draw.positive {q : Nat} (hdraw : Draw q) : 0 < q := by
  have hne : q ≠ 0 := by
    intro hzero
    subst q
    exact hdraw.2 terminal_losing
  omega

theorem Draw.children_not_losing {q : Nat} (hdraw : Draw q) :
    ¬ Losing (A q) ∧ ¬ Losing (B q) := by
  constructor
  · intro hlose
    exact hdraw.1 (Winning.moveA hdraw.positive hlose)
  · intro hlose
    exact hdraw.1 (Winning.moveB hdraw.positive hlose)

theorem Draw.children_not_both_winning {q : Nat} (hdraw : Draw q) :
    ¬ (Winning (A q) ∧ Winning (B q)) := by
  rintro ⟨hwinA, hwinB⟩
  exact hdraw.2 (Losing.replies hdraw.positive hwinA hwinB)

/-- Every DRAW candidate has a legal child which is again a DRAW candidate. -/
theorem Draw.has_draw_child {q : Nat} (hdraw : Draw q) :
    ∃ next, ConjugatedMove next q ∧ Draw next := by
  classical
  by_cases hwinA : Winning (A q)
  · have hwinB : ¬ Winning (B q) := by
      intro h
      exact hdraw.children_not_both_winning ⟨hwinA, h⟩
    refine ⟨B q, ⟨hdraw.positive, Or.inr rfl⟩, ?_⟩
    exact ⟨hwinB, hdraw.children_not_losing.2⟩
  · refine ⟨A q, ⟨hdraw.positive, Or.inl rfl⟩, ?_⟩
    exact ⟨hwinA, hdraw.children_not_losing.1⟩

theorem winning_of_not_draw_and_not_losing {q : Nat}
    (notDraw : ¬ Draw q) (notLosing : ¬ Losing q) : Winning q := by
  classical
  by_cases winning : Winning q
  · exact winning
  · exact False.elim (notDraw ⟨winning, notLosing⟩)

/-- If the B-child of a DRAW is winning, its A-child is DRAW. -/
theorem Draw.A_of_B_winning {q : Nat} (hdraw : Draw q)
    (winningB : Winning (B q)) : Draw (A q) := by
  have notWinningA : ¬ Winning (A q) := by
    intro winningA
    exact hdraw.children_not_both_winning ⟨winningA, winningB⟩
  exact ⟨notWinningA, hdraw.children_not_losing.1⟩

/-- If the A-child of a DRAW is winning, its B-child is DRAW. -/
theorem Draw.B_of_A_winning {q : Nat} (hdraw : Draw q)
    (winningA : Winning (A q)) : Draw (B q) := by
  have notWinningB : ¬ Winning (B q) := by
    intro winningB
    exact hdraw.children_not_both_winning ⟨winningA, winningB⟩
  exact ⟨notWinningB, hdraw.children_not_losing.2⟩

theorem not_draw_iff_resolved (q : Nat) : ¬ Draw q ↔ Resolved q := by
  classical
  constructor
  · intro hnot
    by_cases hwin : Winning q
    · exact Or.inl hwin
    · right
      by_cases hlose : Losing q
      · exact hlose
      · exact False.elim (hnot ⟨hwin, hlose⟩)
  · intro hresolved hdraw
    cases hresolved with
    | inl hwin => exact hdraw.1 hwin
    | inr hlose => exact hdraw.2 hlose

private theorem outcomeTrees_disjoint_at_total (total : Nat) :
    ∀ {q winningHeight losingHeight : Nat},
      winningHeight + losingHeight = total →
      WinningTree q winningHeight → LosingTree q losingHeight → False := by
  refine Nat.strongRecOn
    (motive := fun total =>
      ∀ {q winningHeight losingHeight : Nat},
        winningHeight + losingHeight = total →
        WinningTree q winningHeight → LosingTree q losingHeight → False)
    total ?_
  intro total ih q winningHeight losingHeight htotal winning losing
  cases winning with
  | moveA nonterminal losingChild =>
      cases losing with
      | terminal => omega
      | replies _ winningA winningB =>
          apply ih _ (by omega) rfl winningA losingChild
  | moveB nonterminal losingChild =>
      cases losing with
      | terminal => omega
      | replies _ winningA winningB =>
          apply ih _ (by omega) rfl winningB losingChild

/-- Finite winning and losing strategy trees are mutually exclusive. -/
theorem Winning.not_losing {q : Nat} (winning : Winning q) : ¬ Losing q := by
  rintro ⟨losingHeight, losingTree⟩
  obtain ⟨winningHeight, winningTree⟩ := winning
  exact outcomeTrees_disjoint_at_total (winningHeight + losingHeight)
    rfl winningTree losingTree

theorem Losing.not_winning {q : Nat} (losing : Losing q) : ¬ Winning q := by
  intro winning
  exact winning.not_losing losing

theorem Losing.children_winning {q : Nat} (losing : Losing q)
    (nonterminal : 0 < q) : Winning (A q) ∧ Winning (B q) := by
  obtain ⟨height, tree⟩ := losing
  cases tree with
  | terminal => omega
  | replies _ replyA replyB =>
      exact ⟨⟨_, replyA⟩, ⟨_, replyB⟩⟩

theorem Winning.B_losing_of_A_not_losing {q : Nat} (winning : Winning q)
    (notLosingA : ¬ Losing (A q)) : Losing (B q) := by
  obtain ⟨height, tree⟩ := winning
  cases tree with
  | moveA _ reply => exact False.elim (notLosingA ⟨_, reply⟩)
  | moveB _ reply => exact ⟨_, reply⟩

theorem Winning.A_losing_of_B_not_losing {q : Nat} (winning : Winning q)
    (notLosingB : ¬ Losing (B q)) : Losing (A q) := by
  obtain ⟨height, tree⟩ := winning
  cases tree with
  | moveA _ reply => exact ⟨_, reply⟩
  | moveB _ reply => exact False.elim (notLosingB ⟨_, reply⟩)

/-- A state packaged together with one exact finite outcome tree. -/
inductive SolvedPosition
  | win {q height : Nat} (tree : WinningTree q height)
  | lose {q height : Nat} (tree : LosingTree q height)

def SolvedPosition.position : SolvedPosition → Nat
  | .win (q := q) _ => q
  | .lose (q := q) _ => q

def SolvedPosition.height : SolvedPosition → Nat
  | .win (height := height) _ => height
  | .lose (height := height) _ => height

theorem solvedPosition_of_resolved {q : Nat} (resolved : Resolved q) :
    ∃ solved : SolvedPosition, solved.position = q := by
  cases resolved with
  | inl winning =>
      obtain ⟨height, tree⟩ := winning
      exact ⟨SolvedPosition.win tree, rfl⟩
  | inr losing =>
      obtain ⟨height, tree⟩ := losing
      exact ⟨SolvedPosition.lose tree, rfl⟩

/--
One move justified by finite optimal-outcome trees. A winning player follows
the selected losing child; at a losing state either legal child is allowed.
-/
inductive OptimalProofStep : SolvedPosition → SolvedPosition → Prop
  | winA {q height : Nat} (nonterminal : 0 < q)
      (reply : LosingTree (A q) height) :
      OptimalProofStep (.lose reply) (.win (.moveA nonterminal reply))
  | winB {q height : Nat} (nonterminal : 0 < q)
      (reply : LosingTree (B q) height) :
      OptimalProofStep (.lose reply) (.win (.moveB nonterminal reply))
  | loseA {q heightA heightB : Nat} (nonterminal : 0 < q)
      (replyA : WinningTree (A q) heightA)
      (replyB : WinningTree (B q) heightB) :
      OptimalProofStep (.win replyA)
        (.lose (.replies nonterminal replyA replyB))
  | loseB {q heightA heightB : Nat} (nonterminal : 0 < q)
      (replyA : WinningTree (A q) heightA)
      (replyB : WinningTree (B q) heightB) :
      OptimalProofStep (.win replyB)
        (.lose (.replies nonterminal replyA replyB))

theorem optimalProofStep_decreases {next current : SolvedPosition}
    (edge : OptimalProofStep next current) :
    next.height < current.height := by
  cases edge with
  | winA => simp [SolvedPosition.height]
  | winB => simp [SolvedPosition.height]
  | loseA _ replyA replyB =>
      simp only [SolvedPosition.height]
      exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  | loseB _ replyA replyB =>
      simp only [SolvedPosition.height]
      exact Nat.lt_succ_of_le (Nat.le_max_right _ _)

theorem optimalProofStep_wellFounded : WellFounded OptimalProofStep := by
  apply Subrelation.wf
    (q := OptimalProofStep)
    (r := InvImage Nat.lt SolvedPosition.height)
  · intro next current edge
    exact optimalProofStep_decreases edge
  · exact InvImage.wf SolvedPosition.height Nat.lt_wfRel.wf

theorem solvedPosition_has_step {current : SolvedPosition}
    (nonterminal : 0 < current.position) :
    ∃ next, OptimalProofStep next current := by
  cases current with
  | win tree =>
      cases tree with
      | moveA h reply => exact ⟨SolvedPosition.lose reply, .winA h reply⟩
      | moveB h reply => exact ⟨SolvedPosition.lose reply, .winB h reply⟩
  | lose tree =>
      cases tree with
      | terminal => simp [SolvedPosition.position] at nonterminal
      | replies h replyA replyB =>
          exact ⟨SolvedPosition.win replyA, .loseA h replyA replyB⟩

/-- No infinite play can follow finite optimal-outcome proof trees. -/
theorem no_infinite_optimal_proof_play (path : Nat → SolvedPosition) :
    ¬ InfiniteDescending OptimalProofStep path := by
  exact wellFounded_noInfiniteDescending optimalProofStep_wellFounded path

/-- General well-founded progress principle. -/
theorem no_bad_of_wellFounded_progress
    {Configuration : Type} {step : Configuration → Configuration → Prop}
    (stepWf : WellFounded step) (bad : Configuration → Prop)
    (progress : ∀ current, bad current →
      ∃ next, step next current ∧ bad next) :
    ∀ current, ¬ bad current := by
  intro current
  refine stepWf.induction (C := fun current => ¬ bad current) current ?_
  intro current ih hbad
  obtain ⟨next, edge, nextBad⟩ := progress current hbad
  exact ih next edge nextBad

theorem no_draw_of_move_wellFounded
    (moveWf : WellFounded ConjugatedMove) :
    ∀ q, ¬ Draw q := by
  apply no_bad_of_wellFounded_progress moveWf Draw
  intro q hdraw
  exact hdraw.has_draw_child

theorem no_draw_of_wellFounded_macro
    {Configuration : Type} {macroStep : Configuration → Configuration → Prop}
    (macroWf : WellFounded macroStep) (bad : Configuration → Prop)
    (lift : ∀ q, Draw q → ∃ configuration, bad configuration)
    (progress : ∀ current, bad current →
      ∃ next, macroStep next current ∧ bad next) :
    ∀ q, ¬ Draw q := by
  have noBad := no_bad_of_wellFounded_progress macroWf bad progress
  intro q hdraw
  obtain ⟨configuration, hbad⟩ := lift q hdraw
  exact noBad configuration hbad

end ThreeNPlusMinusOne
