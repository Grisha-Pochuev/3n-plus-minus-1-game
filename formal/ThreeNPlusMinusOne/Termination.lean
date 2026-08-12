import ThreeNPlusMinusOne.OriginalNormalForm
import ThreeNPlusMinusOne.Refinement

set_option autoImplicit false

/-!
# From conjugated resolution to termination in the original game

The conjugated coordinate `q` represents the ordinary odd-state coordinate
`A q`.  This file transports finite outcome trees along that representation,
then handles an arbitrary ordinary coordinate `m` by observing that both of
its children, `A m` and `A (R m)`, are represented conjugated states.
-/

namespace ThreeNPlusMinusOne

mutual
  inductive CoordinateWinningTree : Nat → Nat → Prop
    | moveA {m height : Nat} (nonterminal : 0 < m)
        (reply : CoordinateLosingTree (A m) height) :
        CoordinateWinningTree m (height + 1)
    | moveR {m height : Nat} (nonterminal : 0 < m)
        (reply : CoordinateLosingTree (A (R m)) height) :
        CoordinateWinningTree m (height + 1)

  inductive CoordinateLosingTree : Nat → Nat → Prop
    | terminal : CoordinateLosingTree 0 0
    | replies {m heightA heightR : Nat} (nonterminal : 0 < m)
        (replyA : CoordinateWinningTree (A m) heightA)
        (replyR : CoordinateWinningTree (A (R m)) heightR) :
        CoordinateLosingTree m (max heightA heightR + 1)
end

def CoordinateWinning (m : Nat) : Prop :=
  ∃ height, CoordinateWinningTree m height

def CoordinateLosing (m : Nat) : Prop :=
  ∃ height, CoordinateLosingTree m height

def CoordinateResolved (m : Nat) : Prop :=
  CoordinateWinning m ∨ CoordinateLosing m

mutual
  theorem WinningTree.toCoordinate {q height : Nat}
      (tree : WinningTree q height) :
      CoordinateWinningTree (A q) height := by
    cases tree with
    | moveA nonterminal reply =>
        exact CoordinateWinningTree.moveA (A_pos nonterminal)
          (LosingTree.toCoordinate reply)
    | moveB nonterminal reply =>
        exact CoordinateWinningTree.moveR (A_pos nonterminal)
          (LosingTree.toCoordinate reply)

  theorem LosingTree.toCoordinate {q height : Nat}
      (tree : LosingTree q height) :
      CoordinateLosingTree (A q) height := by
    cases tree with
    | terminal => simp [A]; exact CoordinateLosingTree.terminal
    | replies nonterminal replyA replyB =>
        exact CoordinateLosingTree.replies (A_pos nonterminal)
          (WinningTree.toCoordinate replyA)
          (WinningTree.toCoordinate replyB)
end

theorem resolved_to_coordinate {q : Nat} (resolved : Resolved q) :
    CoordinateResolved (A q) := by
  cases resolved with
  | inl winning =>
      obtain ⟨height, tree⟩ := winning
      exact Or.inl ⟨height, tree.toCoordinate⟩
  | inr losing =>
      obtain ⟨height, tree⟩ := losing
      exact Or.inr ⟨height, tree.toCoordinate⟩

/-- Resolution of every conjugated state resolves every ordinary coordinate. -/
theorem all_coordinate_resolved
    (allResolved : ∀ q, Resolved q) : ∀ m, CoordinateResolved m := by
  intro m
  by_cases hterminal : m = 0
  · subst m
    exact Or.inr ⟨0, CoordinateLosingTree.terminal⟩
  · have hm : 0 < m := by omega
    have first := resolved_to_coordinate (allResolved m)
    have second := resolved_to_coordinate (allResolved (R m))
    cases first with
    | inr firstLosing =>
        obtain ⟨height, tree⟩ := firstLosing
        exact Or.inl ⟨height + 1,
          CoordinateWinningTree.moveA hm tree⟩
    | inl firstWinning =>
        cases second with
        | inr secondLosing =>
            obtain ⟨height, tree⟩ := secondLosing
            exact Or.inl ⟨height + 1,
              CoordinateWinningTree.moveR hm tree⟩
        | inl secondWinning =>
            obtain ⟨heightA, treeA⟩ := firstWinning
            obtain ⟨heightR, treeR⟩ := secondWinning
            exact Or.inr ⟨max heightA heightR + 1,
              CoordinateLosingTree.replies hm treeA treeR⟩

/-- Every original state is uniquely an ordinary coordinate state. -/
theorem originalState_is_coordinate (state : OriginalState) :
    ∃ m, state = coordinateState m := by
  obtain ⟨m, hvalue⟩ := state.odd
  exact ⟨m, OriginalState.eq_of_value_eq hvalue⟩

def OriginalResolved (state : OriginalState) : Prop :=
  ∃ m, state = coordinateState m ∧ CoordinateResolved m

theorem all_original_resolved
    (allResolved : ∀ q, Resolved q) :
    ∀ state, OriginalResolved state := by
  intro state
  obtain ⟨m, rfl⟩ := originalState_is_coordinate state
  exact ⟨m, rfl, all_coordinate_resolved allResolved m⟩

/-- A coordinate state packaged with one exact finite outcome tree. -/
inductive CoordinateSolvedPosition
  | win {m height : Nat} (tree : CoordinateWinningTree m height)
  | lose {m height : Nat} (tree : CoordinateLosingTree m height)

def CoordinateSolvedPosition.coordinate : CoordinateSolvedPosition → Nat
  | .win (m := m) _ => m
  | .lose (m := m) _ => m

def CoordinateSolvedPosition.height : CoordinateSolvedPosition → Nat
  | .win (height := height) _ => height
  | .lose (height := height) _ => height

def CoordinateSolvedPosition.original : CoordinateSolvedPosition → OriginalState
  | solved => coordinateState solved.coordinate

inductive CoordinateOptimalStep :
    CoordinateSolvedPosition → CoordinateSolvedPosition → Prop
  | winA {m height : Nat} (nonterminal : 0 < m)
      (reply : CoordinateLosingTree (A m) height) :
      CoordinateOptimalStep (.lose reply) (.win (.moveA nonterminal reply))
  | winR {m height : Nat} (nonterminal : 0 < m)
      (reply : CoordinateLosingTree (A (R m)) height) :
      CoordinateOptimalStep (.lose reply) (.win (.moveR nonterminal reply))
  | loseA {m heightA heightR : Nat} (nonterminal : 0 < m)
      (replyA : CoordinateWinningTree (A m) heightA)
      (replyR : CoordinateWinningTree (A (R m)) heightR) :
      CoordinateOptimalStep (.win replyA)
        (.lose (.replies nonterminal replyA replyR))
  | loseR {m heightA heightR : Nat} (nonterminal : 0 < m)
      (replyA : CoordinateWinningTree (A m) heightA)
      (replyR : CoordinateWinningTree (A (R m)) heightR) :
      CoordinateOptimalStep (.win replyR)
        (.lose (.replies nonterminal replyA replyR))

theorem coordinateOptimalStep_decreases {next current : CoordinateSolvedPosition}
    (edge : CoordinateOptimalStep next current) :
    next.height < current.height := by
  cases edge with
  | winA => simp [CoordinateSolvedPosition.height]
  | winR => simp [CoordinateSolvedPosition.height]
  | loseA =>
      simp only [CoordinateSolvedPosition.height]
      exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  | loseR =>
      simp only [CoordinateSolvedPosition.height]
      exact Nat.lt_succ_of_le (Nat.le_max_right _ _)

theorem coordinateOptimalStep_wellFounded : WellFounded CoordinateOptimalStep := by
  apply Subrelation.wf
    (q := CoordinateOptimalStep)
    (r := InvImage Nat.lt CoordinateSolvedPosition.height)
  · intro next current edge
    exact coordinateOptimalStep_decreases edge
  · exact InvImage.wf CoordinateSolvedPosition.height Nat.lt_wfRel.wf

/-- Every proof-tree optimal step is a legal move of the original game. -/
theorem coordinateOptimalStep_is_originalMove
    {next current : CoordinateSolvedPosition}
    (edge : CoordinateOptimalStep next current) :
    OriginalMove current.original next.original := by
  cases edge with
  | winA nonterminal reply => exact coordinateMove_A nonterminal
  | winR nonterminal reply => exact coordinateMove_R nonterminal
  | loseA nonterminal replyA replyR => exact coordinateMove_A nonterminal
  | loseR nonterminal replyA replyR => exact coordinateMove_R nonterminal

/-- Conditional end theorem for every original odd start. -/
theorem DrawMacroRefinement.original_resolved
    (refinement : DrawMacroRefinement) :
    ∀ state, OriginalResolved state := by
  exact all_original_resolved refinement.resolved

/-- No infinite original play can follow the finite optimal proof trees. -/
theorem no_infinite_coordinate_optimal_play
    (path : Nat → CoordinateSolvedPosition) :
    ¬ InfiniteDescending CoordinateOptimalStep path := by
  exact wellFounded_noInfiniteDescending
    coordinateOptimalStep_wellFounded path

end ThreeNPlusMinusOne
