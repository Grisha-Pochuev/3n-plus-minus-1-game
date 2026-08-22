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
  def WinningCertificate.toWinningTree :
      {position height : Nat} → WinningCertificate position height →
        WinningTree position height
    | _, _, .moveA nonterminal reply =>
        WinningTree.moveA nonterminal (LosingCertificate.toLosingTree reply)
    | _, _, .moveB nonterminal reply =>
        WinningTree.moveB nonterminal (LosingCertificate.toLosingTree reply)

  /-- Forget the data-level branch identity and recover the existing finite
  LOSS proposition. -/
  def LosingCertificate.toLosingTree :
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
          have impossible : False := by
            simpa using nonterminal
          exact False.elim impossible
      | replies storedNonterminal replyA replyB =>
          exact ⟨⟨A position, _, replyA⟩, ⟨B position, _, replyB⟩,
            rfl, rfl,
            Nat.succ_le_succ (Nat.le_max_left _ _),
            Nat.succ_le_succ (Nat.le_max_right _ _)⟩

end CertifiedLosingToken

end ThreeNPlusMinusOne
