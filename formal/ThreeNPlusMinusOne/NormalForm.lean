import ThreeNPlusMinusOne.Game

set_option autoImplicit false

/-!
# Alternating-suffix normal form

This file gives an executable, kernel-checked definition of the operation
`R` from `docs/normal-form.md`.  It deliberately scans as many binary digits
as are needed: no fixed residue class is used.

For a positive binary word, deletion always removes its last digit.  If the
new last digit is equal to the deleted digit, the maximal alternating suffix
has ended.  Otherwise the scan continues on the remaining prefix.  Words of
length at most one have empty remainder.
-/

namespace ThreeNPlusMinusOne

/-- Delete the maximal alternating suffix of the binary expansion of `x`. -/
def R (x : Nat) : Nat :=
  if hsmall : x < 2 then
    0
  else
    let y := x / 2
    if x % 2 = y % 2 then y else R y
termination_by x
decreasing_by
  exact Nat.div_lt_self (by omega) (by omega)

theorem R_of_small {x : Nat} (hsmall : x < 2) : R x = 0 := by
  rw [R.eq_1 x, dif_pos hsmall]

theorem R_of_boundary {x : Nat} (hlarge : 2 ≤ x)
    (boundary : x % 2 = (x / 2) % 2) : R x = x / 2 := by
  rw [R.eq_1 x, dif_neg (show ¬ x < 2 by omega), if_pos boundary]

theorem R_of_alternates {x : Nat} (hlarge : 2 ≤ x)
    (alternates : x % 2 ≠ (x / 2) % 2) : R x = R (x / 2) := by
  rw [R.eq_1 x, dif_neg (show ¬ x < 2 by omega), if_neg alternates]

/--
Relational specification of deleting the maximal alternating suffix.

The constructors are the three exhaustive cases of the bit scan: the whole
word is deleted, one final bit is deleted at a repeated-bit boundary, or two
adjacent bits alternate and the scan continues in the prefix.
-/
inductive AlternatingRemainder : Nat → Nat → Prop
  | small {x : Nat} (hsmall : x < 2) : AlternatingRemainder x 0
  | stop {x : Nat} (hlarge : 2 ≤ x)
      (boundary : x % 2 = (x / 2) % 2) :
      AlternatingRemainder x (x / 2)
  | scan {x remainder : Nat} (hlarge : 2 ≤ x)
      (alternates : x % 2 ≠ (x / 2) % 2)
      (rest : AlternatingRemainder (x / 2) remainder) :
      AlternatingRemainder x remainder

/-- The executable operation satisfies the recursive maximal-suffix spec. -/
theorem R_spec (x : Nat) : AlternatingRemainder x (R x) := by
  refine Nat.strongRecOn
    (motive := fun x => AlternatingRemainder x (R x)) x ?_
  intro x ih
  by_cases hsmall : x < 2
  · rw [R_of_small hsmall]
    exact AlternatingRemainder.small hsmall
  · have hx : 2 ≤ x := by omega
    by_cases boundary : x % 2 = (x / 2) % 2
    · rw [R_of_boundary hx boundary]
      exact AlternatingRemainder.stop hx boundary
    · rw [R_of_alternates hx boundary]
      apply AlternatingRemainder.scan hx boundary
      apply ih
      exact Nat.div_lt_self (by omega) (by omega)

/-- The recursive specification determines exactly the executable `R`. -/
theorem AlternatingRemainder.eq_R
    {x remainder : Nat} (h : AlternatingRemainder x remainder) :
    remainder = R x := by
  induction h with
  | small hsmall =>
      exact (R_of_small hsmall).symm
  | stop hlarge boundary =>
      exact (R_of_boundary hlarge boundary).symm
  | scan hlarge alternates rest ih =>
      exact ih.trans (R_of_alternates hlarge alternates).symm

/-- The maximal alternating-suffix remainder is unique. -/
theorem AlternatingRemainder.unique
    {x first second : Nat}
    (hfirst : AlternatingRemainder x first)
    (hsecond : AlternatingRemainder x second) :
    first = second := by
  rw [hfirst.eq_R, hsecond.eq_R]

/-- Deleting a nonempty suffix leaves at most the prefix after one bit. -/
theorem R_le_half (x : Nat) : R x ≤ x / 2 := by
  refine Nat.strongRecOn
    (motive := fun x => R x ≤ x / 2) x ?_
  intro x ih
  by_cases hsmall : x < 2
  · rw [R_of_small hsmall]
    exact Nat.zero_le _
  · have hlarge : 2 ≤ x := by omega
    by_cases boundary : x % 2 = (x / 2) % 2
    · rw [R_of_boundary hlarge boundary]
      exact Nat.le_refl _
    · rw [R_of_alternates hlarge boundary]
      have hprefix : x / 2 < x :=
        Nat.div_lt_self (by omega) (by omega)
      exact Nat.le_trans (ih (x / 2) hprefix) (Nat.div_le_self _ _)

/-- Every positive input strictly decreases under suffix deletion. -/
theorem R_lt_self {x : Nat} (hx : 0 < x) : R x < x := by
  exact Nat.lt_of_le_of_lt (R_le_half x) (Nat.div_lt_self hx (by omega))

/-- Contracting branch in the conjugated game. -/
def B (q : Nat) : Nat :=
  R (A q)

@[simp] theorem R_zero : R 0 = 0 := by
  simp [R]

@[simp] theorem R_one : R 1 = 0 := by
  simp [R]

@[simp] theorem R_two : R 2 = 0 := by
  rw [R]
  simp

@[simp] theorem B_zero : B 0 = 0 := by
  simp [B, A]

@[simp] theorem B_one : B 1 = 0 := by
  simp [B, A]

/-- The second conjugated branch is strictly contracting away from terminal. -/
theorem B_strictly_contracts {q : Nat} (hq : 0 < q) : B q < q := by
  by_cases hqone : q = 1
  · simp [hqone]
  · have hqtwo : 2 ≤ q := by omega
    apply Nat.lt_of_le_of_lt (R_le_half (A q))
    unfold A
    omega

end ThreeNPlusMinusOne
