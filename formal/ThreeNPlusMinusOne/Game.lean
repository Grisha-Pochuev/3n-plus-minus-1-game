import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
# The `3n±1` game: kernel-checked foundations

This file formalizes the state space, the two original signed moves as an
arithmetic relation, and the expanding branch of the binary normal form.

The global no-`DRAW` argument is not yet claimed here.  Its current formal
coverage is recorded in `formal/COVERAGE.md`.
-/

namespace ThreeNPlusMinusOne

/-- An explicit dependency-free predicate for odd natural numbers. -/
def OddNat (n : Nat) : Prop :=
  ∃ k : Nat, n = 2 * k + 1

/-- A legal original-game position is a positive odd natural number. -/
structure OriginalState where
  value : Nat
  positive : 0 < value
  odd : OddNat value

/-- The terminal original-game position. -/
def terminal : OriginalState :=
  ⟨1, by omega, ⟨0, by omega⟩⟩

/--
`RemoveTwos x y` says that `y` is the odd part of the positive integer `x`.
This relational definition avoids hiding uniqueness behind an executable
normalization routine.
-/
def RemoveTwos (x y : Nat) : Prop :=
  OddNat y ∧ ∃ k : Nat, x = 2 ^ k * y

/-- The two signed choices available before removing powers of two. -/
inductive Sign
  | minus
  | plus
  deriving DecidableEq, Repr

/-- The raw value `3n±1` selected by a sign. -/
def rawMove : Sign → Nat → Nat
  | .minus, n => 3 * n - 1
  | .plus, n => 3 * n + 1

/-- Exact legal-move relation for the original game. -/
def OriginalMove (n m : OriginalState) : Prop :=
  n.value ≠ 1 ∧ ∃ s : Sign, RemoveTwos (rawMove s n.value) m.value

/-- Expanding branch in the conjugated coordinate `n = 2q+1`. -/
def A (q : Nat) : Nat :=
  (3 * q + 1) / 2

@[simp] theorem A_even (q : Nat) : A (2 * q) = 3 * q := by
  simp [A]
  omega

@[simp] theorem A_odd (q : Nat) : A (2 * q + 1) = 3 * q + 2 := by
  simp [A]
  omega

theorem A_pos {q : Nat} (hq : 0 < q) : 0 < A q := by
  unfold A
  omega

theorem A_strictly_expands {q : Nat} (hq : 0 < q) : q < A q := by
  unfold A
  omega

/-- Embedding of a conjugated state back into the original odd state space. -/
def embeddedValue (q : Nat) : Nat :=
  2 * A q + 1

theorem embeddedValue_positive (q : Nat) : 0 < embeddedValue q := by
  simp [embeddedValue]

theorem embeddedValue_odd (q : Nat) : OddNat (embeddedValue q) := by
  exact ⟨A q, by simp [embeddedValue]⟩

/-- The original state represented by a conjugated coordinate. -/
def embed (q : Nat) : OriginalState :=
  ⟨embeddedValue q, embeddedValue_positive q, embeddedValue_odd q⟩

@[simp] theorem embeddedValue_even_coordinate (q : Nat) :
    embeddedValue (2 * q) = 6 * q + 1 := by
  simp [embeddedValue]
  omega

@[simp] theorem embeddedValue_odd_coordinate (q : Nat) :
    embeddedValue (2 * q + 1) = 6 * q + 5 := by
  simp [embeddedValue]
  omega

end ThreeNPlusMinusOne
