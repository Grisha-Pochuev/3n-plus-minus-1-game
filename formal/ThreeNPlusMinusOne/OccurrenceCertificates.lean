import ThreeNPlusMinusOne.TokenProvenance

set_option autoImplicit false

/-!
# Data-level finite proof certificates

`WinningTree` and `LosingTree` express finite outcomes as propositions.  The
global no-reseed refinement must additionally retain the *choice* of a finite
tree as data, because a later compatible route can require a different WIN
reply at the same numerical state.  The certificates below duplicate the
finite tree grammar in `Type`, so their branch choices can be carried in a
preinstalled forest.

There is deliberately no conversion from bare `Winning` or `Losing` into a
certificate: extracting a new data-level witness after the future route is
known would be precisely the installation step that the lifecycle proof must
justify.
-/

namespace ThreeNPlusMinusOne

mutual
  /-- A data-level finite WIN certificate with exact height. -/
  inductive WinningCertificate : Nat → Nat → Type
    | moveA {position height : Nat} (nonterminal : 0 < position)
        (reply : LosingCertificate (A position) height) :
        WinningCertificate position (height + 1)
    | moveB {position height : Nat} (nonterminal : 0 < position)
        (reply : LosingCertificate (B position) height) :
        WinningCertificate position (height + 1)

  /-- A data-level finite LOSS certificate with exact height. -/
  inductive LosingCertificate : Nat → Nat → Type
    | terminal : LosingCertificate 0 0
    | replies {position heightA heightB : Nat} (nonterminal : 0 < position)
        (replyA : WinningCertificate (A position) heightA)
        (replyB : WinningCertificate (B position) heightB) :
        LosingCertificate position (max heightA heightB + 1)
end

mutual
  /-- Forget the data-level branch identity and recover the existing finite
  WIN proposition. -/
  theorem WinningCertificate.toWinningTree :
      {position height : Nat} → WinningCertificate position height →
        WinningTree position height
    | _, _, .moveA nonterminal reply =>
        WinningTree.moveA nonterminal (LosingCertificate.toLosingTree reply)
    | _, _, .moveB nonterminal reply =>
        WinningTree.moveB nonterminal (LosingCertificate.toLosingTree reply)

  /-- Forget the data-level branch identity and recover the existing finite
  LOSS proposition. -/
  theorem LosingCertificate.toLosingTree :
      {position height : Nat} → LosingCertificate position height →
        LosingTree position height
    | _, _, .terminal => LosingTree.terminal
    | _, _, .replies nonterminal replyA replyB =>
        LosingTree.replies nonterminal
          (WinningCertificate.toWinningTree replyA)
          (WinningCertificate.toWinningTree replyB)
end

/-- A concrete WIN occurrence whose finite certificate remains data. -/
structure CertifiedWinningToken where
  position : Nat
  height : Nat
  certificate : WinningCertificate position height

/-- A concrete LOSS occurrence whose finite certificate remains data. -/
structure CertifiedLosingToken where
  position : Nat
  height : Nat
  certificate : LosingCertificate position height

namespace CertifiedWinningToken

/-- Erasing the data-level branch choice yields the existing logical token.
This operation is one-way in the formal development. -/
def erase (token : CertifiedWinningToken) : WinningToken :=
  ⟨token.position, token.height,
    WinningCertificate.toWinningTree token.certificate⟩

/-- The selected LOSS reply of a stored WIN certificate is itself a stored
occurrence, so no later proof search is needed to expose it. -/
theorem selected_loss (token : CertifiedWinningToken) :
    ∃ loss : CertifiedLosingToken,
      (loss.position = A token.position ∨ loss.position = B token.position) ∧
        loss.height + 1 = token.height := by
  cases token with
  | mk position height certificate =>
      cases certificate with
      | moveA nonterminal reply =>
          exact ⟨⟨A position, _, reply⟩, Or.inl rfl, rfl⟩
      | moveB nonterminal reply =>
          exact ⟨⟨B position, _, reply⟩, Or.inr rfl, rfl⟩

theorem selected_loss_strict (token : CertifiedWinningToken) :
    ∃ loss : CertifiedLosingToken,
      (loss.position = A token.position ∨ loss.position = B token.position) ∧
        loss.height < token.height := by
  obtain ⟨loss, position, height⟩ := selected_loss token
  exact ⟨loss, position, by omega⟩

end CertifiedWinningToken

namespace CertifiedLosingToken

/-- Erasing the data-level branch choice yields the existing logical token. -/
def erase (token : CertifiedLosingToken) : LosingToken :=
  ⟨token.position, token.height,
    LosingCertificate.toLosingTree token.certificate⟩

/-- Both replies of a nonterminal stored LOSS certificate are already stored
as data-level WIN occurrences. -/
theorem children (token : CertifiedLosingToken)
    (nonterminal : 0 < token.position) :
    ∃ first second : CertifiedWinningToken,
      first.position = A token.position ∧
        second.position = B token.position ∧
          first.height + 1 ≤ token.height ∧
            second.height + 1 ≤ token.height := by
  cases token with
  | mk position height certificate =>
      cases certificate with
      | terminal =>
          simp at nonterminal
      | replies storedNonterminal replyA replyB =>
          exact ⟨⟨A position, _, replyA⟩, ⟨B position, _, replyB⟩,
            rfl, rfl,
            Nat.succ_le_succ (Nat.le_max_left _ _),
            Nat.succ_le_succ (Nat.le_max_right _ _)⟩

/-- A positive legal child of a stored LOSS certificate is an already stored
WIN certificate whose height is lower by at least one. -/
theorem positive_child (token : CertifiedLosingToken)
    {child : Nat} (childPositive : 0 < child)
    (move : child = A token.position ∨ child = B token.position) :
    ∃ childToken : CertifiedWinningToken,
      childToken.position = child ∧ childToken.height + 1 ≤ token.height := by
  cases token with
  | mk position height certificate =>
      cases certificate with
      | terminal =>
          rcases move with move | move <;> simp [A, B] at move <;> omega
      | replies storedNonterminal replyA replyB =>
          rcases move with moveA | moveB
          · subst child
            exact ⟨⟨A position, _, replyA⟩, rfl,
              Nat.succ_le_succ (Nat.le_max_left _ _)⟩
          · subst child
            exact ⟨⟨B position, _, replyB⟩, rfl,
              Nat.succ_le_succ (Nat.le_max_right _ _)⟩

end CertifiedLosingToken

namespace CertifiedWinningToken

/-- A positive common grandchild is extracted directly from the retained
data-level WIN certificate.  In contrast to the proposition-level theorem,
the returned descendant carries its original branch choices as data. -/
theorem common_grandchild (token : CertifiedWinningToken)
    {grandchild : Nat} (grandchildPositive : 0 < grandchild)
    (common : CommonGrandchild grandchild token.position) :
    ∃ descendant : CertifiedWinningToken,
      descendant.position = grandchild ∧
        descendant.height + 2 ≤ token.height := by
  cases token with
  | mk position height certificate =>
      cases certificate with
      | @moveA _ replyHeight nonterminal reply =>
          obtain ⟨descendant, descendantPosition, lower⟩ :=
            CertifiedLosingToken.positive_child
              ⟨A position, _, reply⟩ grandchildPositive common.1
          have replyLower : descendant.height + 1 ≤ replyHeight := by
            simpa using lower
          refine ⟨descendant, descendantPosition, ?_⟩
          change descendant.height + 2 ≤ replyHeight + 1
          omega
      | @moveB _ replyHeight nonterminal reply =>
          obtain ⟨descendant, descendantPosition, lower⟩ :=
            CertifiedLosingToken.positive_child
              ⟨B position, _, reply⟩ grandchildPositive common.2
          have replyLower : descendant.height + 1 ≤ replyHeight := by
            simpa using lower
          refine ⟨descendant, descendantPosition, ?_⟩
          change descendant.height + 2 ≤ replyHeight + 1
          omega

/-- The data-level common-grandchild extraction is a strict height decrease. -/
theorem common_grandchild_strict (token : CertifiedWinningToken)
    {grandchild : Nat} (grandchildPositive : 0 < grandchild)
    (common : CommonGrandchild grandchild token.position) :
    ∃ descendant : CertifiedWinningToken,
      descendant.position = grandchild ∧ descendant.height < token.height := by
  obtain ⟨descendant, position, lower⟩ :=
    token.common_grandchild grandchildPositive common
  exact ⟨descendant, position, by omega⟩

end CertifiedWinningToken

/-- A proof occurrence whose finite branch choices remain available as data. -/
inductive CertifiedProofToken
  | winning (token : CertifiedWinningToken)
  | losing (token : CertifiedLosingToken)

namespace CertifiedProofToken

def position : CertifiedProofToken → Nat
  | .winning token => token.position
  | .losing token => token.position

def height : CertifiedProofToken → Nat
  | .winning token => token.height
  | .losing token => token.height

/-- Forget data-level certificate choices while retaining the existing
occurrence token. -/
def erase : CertifiedProofToken → ProofToken
  | .winning token => .winning token.erase
  | .losing token => .losing token.erase

@[simp]
theorem erase_height (token : CertifiedProofToken) :
    ProofToken.height token.erase = token.height := by
  cases token <;> rfl

end CertifiedProofToken

abbrev CertifiedProofForest := List CertifiedProofToken

namespace CertifiedProofForest

/-- The logical occurrence forest obtained by erasing branch-choice data. -/
def toProofForest (forest : CertifiedProofForest) : ProofForest :=
  forest.map CertifiedProofToken.erase

end CertifiedProofForest

/-- The same well-founded weight used for logical proof tokens, now applied
to data-level proof certificates. -/
def certifiedProofTokenRank (forest : CertifiedProofForest) : Nat :=
  tokenRank (forest.map CertifiedProofToken.height)

theorem certifiedProofTokenRank_toProofForest (forest : CertifiedProofForest) :
    proofTokenRank forest.toProofForest = certifiedProofTokenRank forest := by
  unfold proofTokenRank certifiedProofTokenRank CertifiedProofForest.toProofForest
  apply congrArg tokenRank
  induction forest with
  | nil => rfl
  | cons token forest ih =>
      simp only [List.map_cons, List.cons.injEq, ih, and_true]
      change ProofToken.height (CertifiedProofToken.erase token) =
        CertifiedProofToken.height token
      exact CertifiedProofToken.erase_height token

/-- Replace one retained data-level occurrence by at most two already stored
lower data-level descendants. -/
inductive CertifiedProofTokenReplacement
    (next current : CertifiedProofForest) : Prop where
  | mk (before after : CertifiedProofForest)
      (parent : CertifiedProofToken) (children : CertifiedProofForest)
      (current_eq : current = before ++ parent :: after)
      (next_eq : next = before ++ children ++ after)
      (short : children.length ≤ 2)
      (lower : ∀ child ∈ children,
        CertifiedProofToken.height child < CertifiedProofToken.height parent) :
      CertifiedProofTokenReplacement next current

theorem certifiedProofTokenReplacement_single
    {before after : CertifiedProofForest}
    {parent child : CertifiedProofToken}
    (lower : CertifiedProofToken.height child < CertifiedProofToken.height parent) :
    CertifiedProofTokenReplacement
      (before ++ child :: after) (before ++ parent :: after) := by
  refine ⟨before, after, parent, [child], by simp, by simp, by simp, ?_⟩
  intro token member
  simp only [List.mem_singleton] at member
  subst token
  exact lower

/-- Erasing data-level branch choices takes a data-level replacement to the
already checked logical occurrence replacement. -/
theorem certifiedProofTokenReplacement_toProofTokenReplacement
    {next current : CertifiedProofForest}
    (edge : CertifiedProofTokenReplacement next current) :
    ProofTokenReplacement next.toProofForest current.toProofForest := by
  rcases edge with ⟨before, after, parent, children, currentEq, nextEq,
    short, lower⟩
  refine ⟨before.toProofForest, after.toProofForest, parent.erase,
    children.toProofForest, ?_, ?_, ?_, ?_⟩
  · rw [currentEq]
    simp [CertifiedProofForest.toProofForest]
  · rw [nextEq]
    simp [CertifiedProofForest.toProofForest]
  · simpa [CertifiedProofForest.toProofForest] using short
  · intro child member
    simp only [CertifiedProofForest.toProofForest, List.mem_map] at member
    obtain ⟨storedChild, storedMember, rfl⟩ := member
    simpa using lower storedChild storedMember

theorem certifiedProofTokenReplacement_decreases
    {next current : CertifiedProofForest}
    (edge : CertifiedProofTokenReplacement next current) :
    certifiedProofTokenRank next < certifiedProofTokenRank current := by
  rw [← certifiedProofTokenRank_toProofForest next,
    ← certifiedProofTokenRank_toProofForest current]
  exact proofTokenReplacement_decreases
    (certifiedProofTokenReplacement_toProofTokenReplacement edge)

theorem certifiedProofTokenReplacement_wellFounded :
    WellFounded CertifiedProofTokenReplacement := by
  apply Subrelation.wf
    (q := CertifiedProofTokenReplacement)
    (r := InvImage Nat.lt certifiedProofTokenRank)
  · intro next current edge
    exact certifiedProofTokenReplacement_decreases edge
  · exact InvImage.wf certifiedProofTokenRank Nat.lt_wfRel.wf

/-- A positive common grandchild of a retained data-level WIN occurrence can
replace that occurrence inside a data-level forest, and its erasure is
compatible with the existing proof-token rank. -/
theorem certifiedProofToken_common_grandchild_rank_payment
    {before after : CertifiedProofForest}
    (token : CertifiedWinningToken)
    {grandchild : Nat} (grandchildPositive : 0 < grandchild)
    (common : CommonGrandchild grandchild token.position) :
    ∃ descendant : CertifiedWinningToken,
      descendant.position = grandchild ∧
        certifiedProofTokenRank
            (before ++ CertifiedProofToken.winning descendant :: after) <
          certifiedProofTokenRank
            (before ++ CertifiedProofToken.winning token :: after) := by
  obtain ⟨descendant, descendantPosition, lower⟩ :=
    token.common_grandchild grandchildPositive common
  have descendantLower : descendant.height < token.height := by
    omega
  refine ⟨descendant, descendantPosition, ?_⟩
  apply certifiedProofTokenReplacement_decreases
  apply certifiedProofTokenReplacement_single
  simpa [CertifiedProofToken.height] using descendantLower

/-- Two named data-level occurrences can be replaced in sequence by lower
data-level descendants, paying the same strict certified-forest rank. -/
theorem certifiedProofToken_pair_replacement_decreases
    {before middle after : CertifiedProofForest}
    {firstParent firstChild secondParent secondChild : CertifiedProofToken}
    (firstLower :
      CertifiedProofToken.height firstChild < CertifiedProofToken.height firstParent)
    (secondLower :
      CertifiedProofToken.height secondChild < CertifiedProofToken.height secondParent) :
    certifiedProofTokenRank
        (before ++ [firstChild] ++ middle ++ [secondChild] ++ after) <
      certifiedProofTokenRank
        (before ++ [firstParent] ++ middle ++ [secondParent] ++ after) := by
  have firstStep :
      CertifiedProofTokenReplacement
        (before ++ [firstChild] ++ middle ++ [secondParent] ++ after)
        (before ++ [firstParent] ++ middle ++ [secondParent] ++ after) := by
    simpa [List.append_assoc] using
      (certifiedProofTokenReplacement_single
        (before := before) (after := middle ++ [secondParent] ++ after)
        (parent := firstParent) (child := firstChild) firstLower)
  have secondStep :
      CertifiedProofTokenReplacement
        (before ++ [firstChild] ++ middle ++ [secondChild] ++ after)
        (before ++ [firstChild] ++ middle ++ [secondParent] ++ after) := by
    simpa [List.append_assoc] using
      (certifiedProofTokenReplacement_single
        (before := before ++ [firstChild] ++ middle) (after := after)
        (parent := secondParent) (child := secondChild) secondLower)
  exact Nat.lt_trans (certifiedProofTokenReplacement_decreases secondStep)
    (certifiedProofTokenReplacement_decreases firstStep)

/-- Pair the direct common-grandchild extraction with the data-level forest
rank, preserving the individual branch choices of both descendants. -/
theorem certifiedProofToken_pair_common_grandchild_rank_payment
    {before middle after : CertifiedProofForest}
    (first second : CertifiedWinningToken)
    {firstGrandchild secondGrandchild : Nat}
    (firstPositive : 0 < firstGrandchild)
    (secondPositive : 0 < secondGrandchild)
    (firstCommon : CommonGrandchild firstGrandchild first.position)
    (secondCommon : CommonGrandchild secondGrandchild second.position) :
    ∃ firstDescendant secondDescendant : CertifiedWinningToken,
      firstDescendant.position = firstGrandchild ∧
        secondDescendant.position = secondGrandchild ∧
          firstDescendant.height < first.height ∧
            secondDescendant.height < second.height ∧
              certifiedProofTokenRank
                  (before ++ [CertifiedProofToken.winning firstDescendant] ++
                    middle ++ [CertifiedProofToken.winning secondDescendant] ++
                      after) <
                certifiedProofTokenRank
                  (before ++ [CertifiedProofToken.winning first] ++ middle ++
                    [CertifiedProofToken.winning second] ++ after) := by
  obtain ⟨firstDescendant, firstPosition, firstBound⟩ :=
    first.common_grandchild firstPositive firstCommon
  obtain ⟨secondDescendant, secondPosition, secondBound⟩ :=
    second.common_grandchild secondPositive secondCommon
  have firstLower : firstDescendant.height < first.height := by
    omega
  have secondLower : secondDescendant.height < second.height := by
    omega
  refine ⟨firstDescendant, secondDescendant, firstPosition, secondPosition,
    firstLower, secondLower, ?_⟩
  apply certifiedProofToken_pair_replacement_decreases
  · simpa [CertifiedProofToken.height] using firstLower
  · simpa [CertifiedProofToken.height] using secondLower

end ThreeNPlusMinusOne
