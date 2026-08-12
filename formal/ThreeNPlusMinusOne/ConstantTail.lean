import ThreeNPlusMinusOne.NormalForm

set_option autoImplicit false

/-!
# Constant-tail arithmetic (Section 14)

This file formalizes the universal long-tail recurrence symbolically. The
exponent is not bounded and no residue table is used.
-/

namespace ThreeNPlusMinusOne

def Bit (value : Nat) : Prop :=
  value = 0 ∨ value = 1

def Q (coefficient exponent tailBit : Nat) : Nat :=
  coefficient * 2 ^ exponent - tailBit

private theorem pow_two_split_one {exponent : Nat} (h : 1 ≤ exponent) :
    2 ^ exponent = 2 * 2 ^ (exponent - 1) := by
  obtain ⟨rest, rfl⟩ : ∃ rest, exponent = rest + 1 :=
    ⟨exponent - 1, by omega⟩
  simp [Nat.pow_succ, Nat.mul_comm]

private theorem pow_two_split_two {exponent : Nat} (h : 2 ≤ exponent) :
    2 ^ exponent = 4 * 2 ^ (exponent - 2) := by
  obtain ⟨rest, rfl⟩ : ∃ rest, exponent = rest + 2 :=
    ⟨exponent - 2, by omega⟩
  simp [Nat.pow_add, Nat.mul_comm]

private theorem product_pow_positive {coefficient exponent : Nat}
    (positive : 0 < coefficient) : 0 < coefficient * 2 ^ exponent :=
  Nat.mul_pos positive (Nat.pow_pos (by omega))

/-- Expanding a constant-tail state consumes one tail bit. -/
theorem A_Q {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (hexponent : 1 ≤ exponent) :
    A (Q coefficient exponent tailBit) =
      Q (3 * coefficient) (exponent - 1) tailBit := by
  let base := coefficient * 2 ^ (exponent - 1)
  have hbase : 0 < base := product_pow_positive positive
  have hpow := pow_two_split_one hexponent
  have htwice : coefficient * 2 ^ exponent = 2 * base := by
    simp [base, hpow, Nat.mul_left_comm]
  have htargetZero : Q (3 * coefficient) (exponent - 1) 0 = 3 * base := by
    simp [Q, base, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  have htargetOne : Q (3 * coefficient) (exponent - 1) 1 = 3 * base - 1 := by
    simp [Q, base, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rcases bit with rfl | rfl
  · have hshape : Q coefficient exponent 0 = 2 * base := by
      simp [Q, htwice]
    rw [hshape, A_even, htargetZero]
  · have hshape : Q coefficient exponent 1 = 2 * (base - 1) + 1 := by
      unfold Q
      omega
    rw [hshape, A_odd, htargetOne]
    omega

/-- Two or more constant tail bits make `R` delete exactly one bit. -/
theorem R_Q {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (hexponent : 2 ≤ exponent) :
    R (Q coefficient exponent tailBit) =
      Q coefficient (exponent - 1) tailBit := by
  let base := coefficient * 2 ^ (exponent - 2)
  have hbase : 0 < base := product_pow_positive positive
  have hpowTwo := pow_two_split_two hexponent
  have hpowOne := pow_two_split_one (by omega : 1 ≤ exponent)
  have hfour : coefficient * 2 ^ exponent = 4 * base := by
    simp [base, hpowTwo, Nat.mul_assoc, Nat.mul_comm]
  have htwo : coefficient * 2 ^ (exponent - 1) = 2 * base := by
    obtain ⟨rest, rfl⟩ : ∃ rest, exponent = rest + 2 :=
      ⟨exponent - 2, by omega⟩
    simp [base, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
  rcases bit with rfl | rfl
  · have hshape : Q coefficient exponent 0 = 4 * base := by
      simp [Q, hfour]
    have htarget : Q coefficient (exponent - 1) 0 = 2 * base := by
      simp [Q, htwo]
    have hlarge : 2 ≤ Q coefficient exponent 0 := by omega
    have hboundary :
        Q coefficient exponent 0 % 2 =
          (Q coefficient exponent 0 / 2) % 2 := by
      rw [hshape]
      omega
    rw [R_of_boundary hlarge hboundary, hshape, htarget]
    omega
  · have hshape : Q coefficient exponent 1 = 4 * base - 1 := by
      unfold Q
      omega
    have htarget : Q coefficient (exponent - 1) 1 = 2 * base - 1 := by
      unfold Q
      omega
    have hlarge : 2 ≤ Q coefficient exponent 1 := by omega
    have hboundary :
        Q coefficient exponent 1 % 2 =
          (Q coefficient exponent 1 / 2) % 2 := by
      rw [hshape]
      omega
    rw [R_of_boundary hlarge hboundary, hshape, htarget]
    omega

/-- Section 14: the contracting branch consumes two long-tail bits. -/
theorem B_Q {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (hexponent : 3 ≤ exponent) :
    B (Q coefficient exponent tailBit) =
      Q (3 * coefficient) (exponent - 2) tailBit := by
  unfold B
  rw [A_Q positive bit (by omega)]
  rw [R_Q (by omega) bit (by omega)]
  rw [show exponent - 1 - 1 = exponent - 2 by omega]

theorem constantTail_children {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (hexponent : 3 ≤ exponent) :
    A (Q coefficient exponent tailBit) =
        Q (3 * coefficient) (exponent - 1) tailBit ∧
    B (Q coefficient exponent tailBit) =
        Q (3 * coefficient) (exponent - 2) tailBit := by
  exact ⟨A_Q positive bit (by omega), B_Q positive bit hexponent⟩

/-- Appending the opposite bit extends the alternating suffix by one. -/
theorem R_double_append_opposite {value tailBit : Nat}
    (positive : 0 < value) (bit : Bit tailBit)
    (opposite : value % 2 ≠ tailBit) :
    R (2 * value + tailBit) = R value := by
  have hlarge : 2 ≤ 2 * value + tailBit := by omega
  have hprefix : (2 * value + tailBit) / 2 = value := by
    rcases bit with rfl | rfl <;> omega
  have hlast : (2 * value + tailBit) % 2 = tailBit := by
    rcases bit with rfl | rfl <;> omega
  have halternates :
      (2 * value + tailBit) % 2 ≠
        ((2 * value + tailBit) / 2) % 2 := by
    rw [hlast, hprefix]
    exact fun h => opposite h.symm
  rw [R_of_alternates hlarge halternates, hprefix]

/-- The exponent-one and exponent-two boundary states share their B-child. -/
theorem B_Q_one_eq_two {coefficient tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) :
    B (Q coefficient 1 tailBit) = B (Q coefficient 2 tailBit) := by
  unfold B
  rw [A_Q positive bit (by omega : 1 ≤ 1)]
  rw [A_Q positive bit (by omega : 1 ≤ 2)]
  have coefficientOdd : coefficient % 2 = 1 := by
    obtain ⟨k, rfl⟩ := odd
    omega
  rcases bit with rfl | rfl
  · have hopposite : (3 * coefficient) % 2 ≠ 0 := by omega
    have happend := R_double_append_opposite
      (value := 3 * coefficient) (tailBit := 0)
      (by omega) (Or.inl rfl) hopposite
    simpa [Q, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using happend.symm
  · have hvalue : 0 < 3 * coefficient - 1 := by omega
    have hopposite : (3 * coefficient - 1) % 2 ≠ 1 := by omega
    have happend := R_double_append_opposite
      (value := 3 * coefficient - 1) (tailBit := 1)
      hvalue (Or.inr rfl) hopposite
    have hshape : 2 * (3 * coefficient - 1) + 1 = 6 * coefficient - 1 := by
      omega
    rw [hshape] at happend
    simpa [Q, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using happend.symm

end ThreeNPlusMinusOne
