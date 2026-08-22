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
