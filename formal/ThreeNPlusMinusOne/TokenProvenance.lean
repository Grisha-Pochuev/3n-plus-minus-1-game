import ThreeNPlusMinusOne.Outcome
import ThreeNPlusMinusOne.TokenRank

set_option autoImplicit false

/-!
# Occurrence-preserving proof-token forests

The global routing certificate ranks proof heights, but a height decrease is
sound only when the corresponding proof occurrence was already present.  This
file makes that provenance explicit.  A token stores its exact finite proof
tree, and a forest is a list of such occurrences.  Replacing one occurrence
by at most two proper proof descendants is kernel-checked to decrease the
same additive token rank used by the abstract macro certificate.

This is the reusable token-lifecycle layer for the remaining semantic
refinement.  It does not install a token at a fresh state; callers must supply
the incoming occurrence explicitly.
-/

namespace ThreeNPlusMinusOne

structure WinningToken where
  position : Nat
  height : Nat
  tree : WinningTree position height

structure LosingToken where
  position : Nat
  height : Nat
  tree : LosingTree position height

inductive ProofToken
  | winning (token : WinningToken)
  | losing (token : LosingToken)

namespace ProofToken

def position : ProofToken → Nat
  | .winning token => token.position
  | .losing token => token.position

def height : ProofToken → Nat
  | .winning token => token.height
  | .losing token => token.height

end ProofToken

abbrev ProofForest := List ProofToken

def proofTokenRank (forest : ProofForest) : Nat :=
  tokenRank (forest.map ProofToken.height)

namespace WinningToken

/-- Every retained WIN occurrence exposes its selected LOSS proof child. -/
theorem selected_loss (token : WinningToken) :
    ∃ loss : LosingToken,
      (loss.position = A token.position ∨ loss.position = B token.position) ∧
        loss.height + 1 = token.height := by
  cases token with
  | mk position height tree =>
      cases tree with
      | moveA nonterminal reply =>
          exact ⟨⟨A position, _, reply⟩, Or.inl rfl, rfl⟩
      | moveB nonterminal reply =>
          exact ⟨⟨B position, _, reply⟩, Or.inr rfl, rfl⟩

theorem selected_loss_strict (token : WinningToken) :
    ∃ loss : LosingToken,
      (loss.position = A token.position ∨ loss.position = B token.position) ∧
        loss.height < token.height := by
  obtain ⟨loss, child, height⟩ := selected_loss token
  exact ⟨loss, child, by omega⟩

/-- A retained WIN token is necessarily nonterminal. -/
theorem positive (token : WinningToken) : 0 < token.position := by
  cases token with
  | mk position height tree =>
      cases tree with
      | moveA nonterminal _ => exact nonterminal
      | moveB nonterminal _ => exact nonterminal

/- A common grandchild can replace the retained WIN occurrence by an exact
   lower occurrence, rather than by a merely numerical state. -/
theorem common_grandchild
    (token : WinningToken) {grandchild : Nat}
    (grandchildPositive : 0 < grandchild)
    (common : CommonGrandchild grandchild token.position) :
    ∃ descendant : WinningToken,
      descendant.position = grandchild ∧
        descendant.height + 2 ≤ token.height := by
  obtain ⟨height, tree, lower⟩ := WinningTree.commonGrandchild_lower
    token.tree grandchildPositive common
  exact ⟨⟨grandchild, height, tree⟩, rfl, lower⟩

end WinningToken

namespace LosingToken

/-- Every retained LOSS occurrence carries both of its WIN children. -/
theorem children (token : LosingToken) :
    0 < token.position →
    ∃ first second : WinningToken,
      first.position = A token.position ∧
        second.position = B token.position ∧
          first.height + 1 ≤ token.height ∧
          second.height + 1 ≤ token.height := by
  intro nonterminal
  cases token with
  | mk position height tree =>
      cases tree with
      | terminal =>
          simp_all
      | replies nonterminal replyA replyB =>
          exact ⟨⟨A position, _, replyA⟩, ⟨B position, _, replyB⟩,
            rfl, rfl,
            Nat.succ_le_succ (Nat.le_max_left _ _),
            Nat.succ_le_succ (Nat.le_max_right _ _)⟩

theorem child_strict (token : LosingToken) (nonterminal : 0 < token.position) :
    ∃ first second : WinningToken,
      first.position = A token.position ∧
        second.position = B token.position ∧
          first.height < token.height ∧ second.height < token.height := by
  obtain ⟨first, second, firstPosition, secondPosition, firstHeight,
    secondHeight⟩ := children token nonterminal
  exact ⟨first, second, firstPosition, secondPosition, by omega, by omega⟩

end LosingToken

/-- Replace one exact proof occurrence by a short list of lower occurrences. -/
def ProofTokenReplacement (next current : ProofForest) : Prop :=
  ∃ before after parent children,
    current = before ++ parent :: after ∧
      next = before ++ children ++ after ∧
        children.length ≤ 2 ∧
          ∀ child ∈ children, ProofToken.height child < ProofToken.height parent

theorem proofTokenReplacement_single
    {before after : ProofForest} {parent child : ProofToken}
    (lower : ProofToken.height child < ProofToken.height parent) :
    ProofTokenReplacement
      (before ++ child :: after) (before ++ parent :: after) := by
  refine ⟨before, after, parent, [child], by simp, by simp, by simp, ?_⟩
  intro token member
  simp only [List.mem_singleton] at member
  subst token
  exact lower

theorem proofTokenReplacement_decreases
    {next current : ProofForest} (edge : ProofTokenReplacement next current) :
    proofTokenRank next < proofTokenRank current := by
  obtain ⟨before, after, parent, children, rfl, rfl, short, lower⟩ := edge
  have hlocal : tokenRank (children.map ProofToken.height) <
      tokenWeight (ProofToken.height parent) := by
    apply short_lower_tokenRank_lt
    · simpa using short
    intro child member
    simp only [List.mem_map] at member
    obtain ⟨child, member, rfl⟩ := member
    exact lower child member
  simp only [proofTokenRank, tokenRank, List.map_append, List.sum_append,
    List.map_cons, List.sum_cons]
  simp only [tokenRank] at hlocal
  omega

theorem proofToken_common_grandchild_rank_payment
    {before after : ProofForest} (token : WinningToken)
    {grandchild : Nat} (grandchildPositive : 0 < grandchild)
    (common : CommonGrandchild grandchild token.position) :
    ∃ descendant : WinningToken,
      descendant.position = grandchild ∧
        proofTokenRank
            (before ++ ProofToken.winning descendant :: after) <
          proofTokenRank
            (before ++ ProofToken.winning token :: after) := by
  obtain ⟨descendant, position, lower⟩ := token.common_grandchild
    grandchildPositive common
  refine ⟨descendant, position, ?_⟩
  apply proofTokenReplacement_decreases
  apply proofTokenReplacement_single
  have hdesc : descendant.height < token.height := by omega
  simpa [ProofToken.height] using hdesc

/-- Replacing two already retained occurrences by two lower occurrences pays
the same forest rank.  This is intentionally a replacement of named tokens,
not an installation of finite outcomes at fresh positions. -/
theorem proofToken_pair_replacement_decreases
    {before middle after : ProofForest}
    {firstParent firstChild secondParent secondChild : ProofToken}
    (firstLower : ProofToken.height firstChild < ProofToken.height firstParent)
    (secondLower : ProofToken.height secondChild < ProofToken.height secondParent) :
    proofTokenRank
        (before ++ [firstChild] ++ middle ++ [secondChild] ++ after) <
      proofTokenRank
        (before ++ [firstParent] ++ middle ++ [secondParent] ++ after) := by
  have firstStep :
      ProofTokenReplacement
        (before ++ [firstChild] ++ middle ++ [secondParent] ++ after)
        (before ++ [firstParent] ++ middle ++ [secondParent] ++ after) := by
    simpa [List.append_assoc] using
      (proofTokenReplacement_single
        (before := before) (after := middle ++ [secondParent] ++ after)
        (parent := firstParent) (child := firstChild) firstLower)
  have secondStep :
      ProofTokenReplacement
        (before ++ [firstChild] ++ middle ++ [secondChild] ++ after)
        (before ++ [firstChild] ++ middle ++ [secondParent] ++ after) := by
    simpa [List.append_assoc] using
      (proofTokenReplacement_single
        (before := before ++ [firstChild] ++ middle) (after := after)
        (parent := secondParent) (child := secondChild) secondLower)
  exact Nat.lt_trans (proofTokenReplacement_decreases secondStep)
    (proofTokenReplacement_decreases firstStep)

/-- Two retained WIN tokens can be replaced together by positive common
grandchildren of their respective positions.  The result keeps the exact
descendant occurrences and proves the forest-rank payment in one statement. -/
theorem proofToken_pair_common_grandchild_rank_payment
    {before middle after : ProofForest}
    (first second : WinningToken)
    {firstGrandchild secondGrandchild : Nat}
    (firstPositive : 0 < firstGrandchild)
    (secondPositive : 0 < secondGrandchild)
    (firstCommon : CommonGrandchild firstGrandchild first.position)
    (secondCommon : CommonGrandchild secondGrandchild second.position) :
    ∃ firstDescendant secondDescendant : WinningToken,
      firstDescendant.position = firstGrandchild ∧
        secondDescendant.position = secondGrandchild ∧
          proofTokenRank
              (before ++ [ProofToken.winning firstDescendant] ++ middle ++
                [ProofToken.winning secondDescendant] ++ after) <
            proofTokenRank
              (before ++ [ProofToken.winning first] ++ middle ++
                [ProofToken.winning second] ++ after) := by
  obtain ⟨firstDescendant, firstPosition, firstBound⟩ :=
    first.common_grandchild firstPositive firstCommon
  obtain ⟨secondDescendant, secondPosition, secondBound⟩ :=
    second.common_grandchild secondPositive secondCommon
  refine ⟨firstDescendant, secondDescendant, firstPosition, secondPosition, ?_⟩
  apply proofToken_pair_replacement_decreases
  · simpa [ProofToken.height] using
      (show firstDescendant.height < first.height by omega)
  · simpa [ProofToken.height] using
      (show secondDescendant.height < second.height by omega)

theorem proofTokenReplacement_wellFounded :
    WellFounded ProofTokenReplacement := by
  apply Subrelation.wf
    (q := ProofTokenReplacement)
    (r := InvImage Nat.lt proofTokenRank)
  · intro next current edge
    exact proofTokenReplacement_decreases edge
  · exact InvImage.wf proofTokenRank Nat.lt_wfRel.wf

end ThreeNPlusMinusOne
