import ThreeNPlusMinusOne.OccurrenceRefinement

set_option autoImplicit false

/-!
# First-exit provenance for finite proof trees

A finite WIN/LOSS proof tree need not contain every legal game continuation:
at a WIN node it contains exactly its selected LOSS reply.  This file makes
the resulting first-exit principle explicit.  A legal path starting at a
retained finite tree either stays inside that tree, or exposes a strictly
lower selected LOSS occurrence before it can leave.  The result records a
real descendant token; it does not authorize discarding it or installing an
unrelated finite witness later.
-/

namespace ThreeNPlusMinusOne

/-- A finite sequence of consecutive legal conjugated moves.  Singleton and
empty sequences are paths, while every longer sequence records its first
move and then its suffix. -/
def GamePath : List Nat → Prop
  | [] => True
  | _ :: [] => True
  | current :: next :: rest =>
      ConjugatedMove next current ∧ GamePath (next :: rest)

mutual
  /-- A path is covered by a WIN proof tree when it follows the one selected
  LOSS reply at every WIN node and either reply at every LOSS node. -/
  inductive WinningTreeCovers :
      {position height : Nat} → WinningTree position height → List Nat → Prop
    | stop {position height : Nat} (tree : WinningTree position height) :
        WinningTreeCovers tree [position]
    | moveA {position height : Nat} (nonterminal : 0 < position)
        (reply : LosingTree (A position) height) {path : List Nat}
        (covered : LosingTreeCovers reply path) :
        WinningTreeCovers (WinningTree.moveA nonterminal reply) (position :: path)
    | moveB {position height : Nat} (nonterminal : 0 < position)
        (reply : LosingTree (B position) height) {path : List Nat}
        (covered : LosingTreeCovers reply path) :
        WinningTreeCovers (WinningTree.moveB nonterminal reply) (position :: path)

  /-- A path is covered by a LOSS proof tree when it follows either available
  WIN reply at every nonterminal LOSS node. -/
  inductive LosingTreeCovers :
      {position height : Nat} → LosingTree position height → List Nat → Prop
    | stop {position height : Nat} (tree : LosingTree position height) :
        LosingTreeCovers tree [position]
    | repliesA {position heightA heightB : Nat} (nonterminal : 0 < position)
        (replyA : WinningTree (A position) heightA)
        (replyB : WinningTree (B position) heightB) {path : List Nat}
        (covered : WinningTreeCovers replyA path) :
        LosingTreeCovers (LosingTree.replies nonterminal replyA replyB)
          (position :: path)
    | repliesB {position heightA heightB : Nat} (nonterminal : 0 < position)
        (replyA : WinningTree (A position) heightA)
        (replyB : WinningTree (B position) heightB) {path : List Nat}
        (covered : WinningTreeCovers replyB path) :
        LosingTreeCovers (LosingTree.replies nonterminal replyA replyB)
          (position :: path)
end

/-- Which finite outcome is carried at the current endpoint of a route. -/
inductive RouteKind
  | winning
  | losing

/-- A finite alternating route carrying the finite evidence needed to realize
it as a compatible proof tree.  At a LOSS step the existing LOSS witness
contains both child witnesses, so the route need name only the selected next
child. -/
inductive FiniteOutcomeRoute : RouteKind → Nat → List Nat → Prop
  | winningStop {position : Nat} (winning : Winning position) :
      FiniteOutcomeRoute .winning position [position]
  | winningStep {position next : Nat} {rest : List Nat}
      (move : ConjugatedMove next position)
      (tail : FiniteOutcomeRoute .losing next (next :: rest)) :
      FiniteOutcomeRoute .winning position (position :: next :: rest)
  | losingStop {position : Nat} (losing : Losing position) :
      FiniteOutcomeRoute .losing position [position]
  | losingStep {position next : Nat} {rest : List Nat}
      (losing : Losing position) (move : ConjugatedMove next position)
      (tail : FiniteOutcomeRoute .winning next (next :: rest)) :
      FiniteOutcomeRoute .losing position (position :: next :: rest)

/-- A compatible finite proof tree together with its exact covered route. -/
inductive RouteTree : RouteKind → Nat → List Nat → Prop
  | winning {position height : Nat} {path : List Nat}
      (tree : WinningTree position height)
      (covers : WinningTreeCovers tree path) :
      RouteTree .winning position path
  | losing {position height : Nat} {path : List Nat}
      (tree : LosingTree position height)
      (covers : LosingTreeCovers tree path) :
      RouteTree .losing position path

/-- Every finite alternating route can be realized by a finite proof tree
that covers exactly that route.  The constructed tree can differ from, and
be taller than, a previously retained tree at the same numerical state; this
theorem therefore creates no rank-replacement permission by itself. -/
theorem FiniteOutcomeRoute.realize
    {kind : RouteKind} {position : Nat} {path : List Nat}
    (route : FiniteOutcomeRoute kind position path) :
    RouteTree kind position path := by
  induction route with
  | winningStop winning =>
      obtain ⟨height, tree⟩ := winning
      exact RouteTree.winning tree (WinningTreeCovers.stop tree)
  | winningStep move tail ih =>
      cases ih with
      | losing tree covers =>
          unfold ConjugatedMove at move
          rcases move with ⟨nonterminal, nextA | nextB⟩
          · subst next
            exact RouteTree.winning (WinningTree.moveA nonterminal tree)
              (WinningTreeCovers.moveA nonterminal tree covers)
          · subst next
            exact RouteTree.winning (WinningTree.moveB nonterminal tree)
              (WinningTreeCovers.moveB nonterminal tree covers)
  | losingStop losing =>
      obtain ⟨height, tree⟩ := losing
      exact RouteTree.losing tree (LosingTreeCovers.stop tree)
  | losingStep losing move tail ih =>
      cases ih with
      | winning tree covers =>
          unfold ConjugatedMove at move
          rcases move with ⟨nonterminal, nextA | nextB⟩
          · subst next
            obtain ⟨_, otherWinning⟩ := losing.children_winning nonterminal
            obtain ⟨_, otherTree⟩ := otherWinning
            exact RouteTree.losing
              (LosingTree.replies nonterminal tree otherTree)
              (LosingTreeCovers.repliesA nonterminal tree otherTree covers)
          · subst next
            obtain ⟨otherWinning, _⟩ := losing.children_winning nonterminal
            obtain ⟨_, otherTree⟩ := otherWinning
            exact RouteTree.losing
              (LosingTree.replies nonterminal otherTree tree)
              (LosingTreeCovers.repliesB nonterminal otherTree tree covers)

private theorem proofTree_covers_or_lower_loss_by_height :
    ∀ height : Nat,
      (∀ {position : Nat} (tree : WinningTree position height)
          {rest : List Nat}, GamePath (position :: rest) →
          WinningTreeCovers tree (position :: rest) ∨
            ∃ loss : LosingToken, loss.height < height) ∧
      (∀ {position : Nat} (tree : LosingTree position height)
          {rest : List Nat}, GamePath (position :: rest) →
          LosingTreeCovers tree (position :: rest) ∨
            ∃ loss : LosingToken, loss.height < height) := by
  intro height
  induction height using Nat.strongRecOn with
  | ind height ih =>
      constructor
      · intro position tree rest path
        let token : WinningToken := ⟨position, height, tree⟩
        cases rest with
        | nil =>
            exact Or.inl (WinningTreeCovers.stop tree)
        | cons next rest =>
            change ConjugatedMove next position ∧ GamePath (next :: rest) at path
            rcases path with ⟨move, tailPath⟩
            unfold ConjugatedMove at move
            cases tree with
            | @moveA _ childHeight nonterminal reply =>
                rcases move.2 with nextA | nextB
                · subst next
                  obtain covered | lower :=
                    (ih childHeight (by omega)).2 reply tailPath
                  · exact Or.inl
                      (WinningTreeCovers.moveA nonterminal reply covered)
                  · rcases lower with ⟨loss, lossLower⟩
                    exact Or.inr ⟨loss, by omega⟩
                · subst next
                  obtain ⟨loss, _, lossLower⟩ := token.selected_loss_strict
                  exact Or.inr ⟨loss, by simpa [token] using lossLower⟩
            | @moveB _ childHeight nonterminal reply =>
                rcases move.2 with nextA | nextB
                · subst next
                  obtain ⟨loss, _, lossLower⟩ := token.selected_loss_strict
                  exact Or.inr ⟨loss, by simpa [token] using lossLower⟩
                · subst next
                  obtain covered | lower :=
                    (ih childHeight (by omega)).2 reply tailPath
                  · exact Or.inl
                      (WinningTreeCovers.moveB nonterminal reply covered)
                  · rcases lower with ⟨loss, lossLower⟩
                    exact Or.inr ⟨loss, by omega⟩
      · intro position tree rest path
        cases rest with
        | nil =>
            exact Or.inl (LosingTreeCovers.stop tree)
        | cons next rest =>
            change ConjugatedMove next position ∧ GamePath (next :: rest) at path
            rcases path with ⟨move, tailPath⟩
            unfold ConjugatedMove at move
            cases tree with
            | terminal =>
                omega
            | @replies _ heightA heightB nonterminal replyA replyB =>
                rcases move.2 with nextA | nextB
                · subst next
                  obtain covered | lower :=
                    (ih heightA (by omega)).1 replyA tailPath
                  · exact Or.inl
                      (LosingTreeCovers.repliesA nonterminal replyA replyB covered)
                  · rcases lower with ⟨loss, lossLower⟩
                    exact Or.inr ⟨loss, by omega⟩
                · subst next
                  obtain covered | lower :=
                    (ih heightB (by omega)).1 replyB tailPath
                  · exact Or.inl
                      (LosingTreeCovers.repliesB nonterminal replyA replyB covered)
                  · rcases lower with ⟨loss, lossLower⟩
                    exact Or.inr ⟨loss, by omega⟩

/-- First-exit provenance for a retained WIN tree.  If a legal path from its
root is not covered by the selected finite proof tree, an exact selected LOSS
subtree of strictly smaller height has already been exposed. -/
theorem WinningTree.covers_or_lower_loss
    {position height : Nat} (tree : WinningTree position height)
    {rest : List Nat} (path : GamePath (position :: rest)) :
    WinningTreeCovers tree (position :: rest) ∨
      ∃ loss : LosingToken, loss.height < height := by
  exact (proofTree_covers_or_lower_loss_by_height height).1 tree path

/-- The companion first-exit statement for a LOSS tree.  Both immediate
children are present in a LOSS tree, so any exit occurs strictly lower in one
of its retained WIN replies. -/
theorem LosingTree.covers_or_lower_loss
    {position height : Nat} (tree : LosingTree position height)
    {rest : List Nat} (path : GamePath (position :: rest)) :
    LosingTreeCovers tree (position :: rest) ∨
      ∃ loss : LosingToken, loss.height < height := by
  exact (proofTree_covers_or_lower_loss_by_height height).2 tree path

/-- The first-exit alternative can be stated directly from an occurrence
token: a retained WIN token either covers the legal path or yields a proper
retained LOSS descendant. -/
theorem WinningToken.covers_path_or_lower_loss
    (token : WinningToken) {rest : List Nat}
    (path : GamePath (token.position :: rest)) :
    WinningTreeCovers token.tree (token.position :: rest) ∨
      ∃ loss : LosingToken, loss.height < token.height := by
  exact token.tree.covers_or_lower_loss path

/-- If a legal path leaves a retained WIN proof tree, the exposed selected
LOSS occurrence can be registered immediately as an exact lower
occurrence-forest replacement.  The covered-path alternative keeps the
existing proof tree unchanged. -/
theorem WinningToken.covers_path_or_lower_loss_outer_step
    (token : WinningToken) {rest : List Nat}
    (path : GamePath (token.position :: rest))
    {before after innerForest : ProofForest}
    (base : MacroConfiguration) :
    WinningTreeCovers token.tree (token.position :: rest) ∨
      ∃ loss : LosingToken,
        loss.height < token.height ∧
          OccurrenceMacroStep
            { base := base
              outerForest := before ++ [ProofToken.losing loss] ++ after
              innerForest := innerForest }
            { base := base
              outerForest := before ++ [ProofToken.winning token] ++ after
              innerForest := innerForest } := by
  obtain covered | ⟨loss, lower⟩ := token.covers_path_or_lower_loss path
  · exact Or.inl covered
  · refine Or.inr ⟨loss, lower, ?_⟩
    refine OccurrenceMacroStep.outerForest
      (next :=
        { base := base
          outerForest := before ++ [ProofToken.losing loss] ++ after
          innerForest := innerForest })
      (current :=
        { base := base
          outerForest := before ++ [ProofToken.winning token] ++ after
          innerForest := innerForest })
      rfl rfl ?_
    simpa [List.append_assoc] using
      (proofTokenReplacement_single
        (before := before) (after := after)
        (parent := ProofToken.winning token)
        (child := ProofToken.losing loss)
        (by simpa [ProofToken.height] using lower))

end ThreeNPlusMinusOne
