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
      | moveA nonterminal reply =>
          obtain ⟨descendant, descendantPosition, lower⟩ :=
            CertifiedLosingToken.positive_child
              ⟨A position, _, reply⟩ grandchildPositive common.1
          exact ⟨descendant, descendantPosition, by omega⟩
      | moveB nonterminal reply =>
          obtain ⟨descendant, descendantPosition, lower⟩ :=
            CertifiedLosingToken.positive_child
              ⟨B position, _, reply⟩ grandchildPositive common.2
          exact ⟨descendant, descendantPosition, by omega⟩

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

end ThreeNPlusMinusOne
