import ThreeNPlusMinusOne.ConstantTailBounds
import ThreeNPlusMinusOne.OriginalNormalForm

set_option autoImplicit false

/-!
# Existence and uniqueness of canonical constant-tail coordinates
-/

namespace ThreeNPlusMinusOne

private theorem tailBit_of_coordinates
    {state coefficient exponent tailBit : Nat}
    (coordinates : IsConstantTail state coefficient exponent tailBit) :
    state % 2 = tailBit := by
  have hexponent := coordinates.exponentPositive
  have hsplit : 2 ^ exponent = 2 * 2 ^ (exponent - 1) := by
    obtain ⟨rest, rfl⟩ : ∃ rest, exponent = rest + 1 :=
      ⟨exponent - 1, by omega⟩
    simp [Nat.pow_succ, Nat.mul_comm]
  have hbase : 0 < coefficient * 2 ^ (exponent - 1) :=
    Nat.mul_pos coordinates.positive (Nat.pow_pos (by decide))
  rcases coordinates.bit with rfl | rfl
  · rw [coordinates.equation]
    have hshape : Q coefficient exponent 0 =
        2 * (coefficient * 2 ^ (exponent - 1)) := by
      simp [Q, hsplit, Nat.mul_left_comm]
    rw [hshape]
    omega
  · rw [coordinates.equation]
    unfold Q
    rw [hsplit]
    have hshape : coefficient * (2 * 2 ^ (exponent - 1)) =
        2 * (coefficient * 2 ^ (exponent - 1)) := by
      simp [Nat.mul_left_comm]
    rw [hshape]
    omega

private theorem coordinates_removeTwos
    {state coefficient exponent tailBit : Nat}
    (coordinates : IsConstantTail state coefficient exponent tailBit) :
    RemoveTwos (state + tailBit) coefficient := by
  refine ⟨coordinates.odd, exponent, ?_⟩
  rw [coordinates.equation]
  rcases coordinates.bit with rfl | rfl
  · simp [Q, Nat.mul_comm]
  · unfold Q
    have hpositive : 0 < coefficient * 2 ^ exponent :=
      Nat.mul_pos coordinates.positive (Nat.pow_pos (by decide))
    have hcomm : coefficient * 2 ^ exponent = 2 ^ exponent * coefficient :=
      Nat.mul_comm _ _
    omega

private theorem coordinates_product
    {state coefficient exponent tailBit : Nat}
    (coordinates : IsConstantTail state coefficient exponent tailBit) :
    state + tailBit = coefficient * 2 ^ exponent := by
  rw [coordinates.equation]
  rcases coordinates.bit with rfl | rfl
  · simp [Q]
  · unfold Q
    have hpositive : 0 < coefficient * 2 ^ exponent :=
      Nat.mul_pos coordinates.positive (Nat.pow_pos (by decide))
    omega

private theorem two_pow_strict {lower upper : Nat} (h : lower < upper) :
    2 ^ lower < 2 ^ upper := by
  induction upper generalizing lower with
  | zero => omega
  | succ upper ih =>
      by_cases heq : lower = upper
      · subst lower
        rw [Nat.pow_succ]
        have hpositive : 0 < 2 ^ upper := Nat.pow_pos (by decide)
        omega
      · have hlower : lower < upper := by omega
        have hprevious := ih hlower
        rw [Nat.pow_succ]
        have hpositive : 0 < 2 ^ upper := Nat.pow_pos (by decide)
        omega

private theorem two_pow_injective {first second : Nat}
    (equal : 2 ^ first = 2 ^ second) : first = second := by
  rcases Nat.lt_trichotomy first second with hlt | heq | hgt
  · exact False.elim ((Nat.ne_of_lt (two_pow_strict hlt)) equal)
  · exact heq
  · exact False.elim ((Nat.ne_of_gt (two_pow_strict hgt)) equal)

/-- Every positive state has canonical constant-tail coordinates. -/
theorem constantTailCoordinates_exists {state : Nat} (positive : 0 < state) :
    ∃ coefficient exponent tailBit,
      IsConstantTail state coefficient exponent tailBit := by
  by_cases heven : state % 2 = 0
  · obtain ⟨coefficient, hremove⟩ :=
      RemoveTwos.exists_of_positive positive
    obtain ⟨odd, exponent, hequation⟩ := hremove
    have exponentPositive : 1 ≤ exponent := by
      by_cases hzero : exponent = 0
      · subst exponent
        simp only [Nat.pow_zero, Nat.one_mul] at hequation
        obtain ⟨k, hk⟩ := odd
        rw [hequation, hk] at heven
        omega
      · omega
    exact ⟨coefficient, exponent, 0,
      ⟨by obtain ⟨k, rfl⟩ := odd; omega,
        odd, exponentPositive, Or.inl rfl,
        by simpa [Q, Nat.mul_comm] using hequation⟩⟩
  · have hoddState : state % 2 = 1 := by omega
    have nextPositive : 0 < state + 1 := by omega
    obtain ⟨coefficient, hremove⟩ :=
      RemoveTwos.exists_of_positive nextPositive
    obtain ⟨odd, exponent, hequation⟩ := hremove
    have exponentPositive : 1 ≤ exponent := by
      by_cases hzero : exponent = 0
      · subst exponent
        simp only [Nat.pow_zero, Nat.one_mul] at hequation
        obtain ⟨k, hk⟩ := odd
        omega
      · omega
    have coefficientPositive : 0 < coefficient := by
      obtain ⟨k, rfl⟩ := odd
      omega
    refine ⟨coefficient, exponent, 1,
      ⟨coefficientPositive, odd, exponentPositive, Or.inr rfl, ?_⟩⟩
    unfold Q
    have hcomm : coefficient * 2 ^ exponent = 2 ^ exponent * coefficient :=
      Nat.mul_comm _ _
    omega

/-- The coefficient, exponent, and tail bit in those coordinates are unique. -/
theorem IsConstantTail.unique
    {state firstCoefficient firstExponent firstBit
      secondCoefficient secondExponent secondBit : Nat}
    (first : IsConstantTail state firstCoefficient firstExponent firstBit)
    (second : IsConstantTail state secondCoefficient secondExponent secondBit) :
    firstCoefficient = secondCoefficient ∧
      firstExponent = secondExponent ∧ firstBit = secondBit := by
  have hfirstBit := tailBit_of_coordinates first
  have hsecondBit := tailBit_of_coordinates second
  have hbit : firstBit = secondBit := by omega
  have hsecondRemove := coordinates_removeTwos second
  rw [← hbit] at hsecondRemove
  have hcoefficient : firstCoefficient = secondCoefficient :=
    RemoveTwos.unique (coordinates_removeTwos first) hsecondRemove
  have hpowers : 2 ^ firstExponent = 2 ^ secondExponent := by
    have heq : firstCoefficient * 2 ^ firstExponent =
        firstCoefficient * 2 ^ secondExponent := by
      calc
        firstCoefficient * 2 ^ firstExponent = state + firstBit :=
          (coordinates_product first).symm
        _ = state + secondBit := by rw [hbit]
        _ = secondCoefficient * 2 ^ secondExponent := coordinates_product second
        _ = firstCoefficient * 2 ^ secondExponent := by rw [hcoefficient]
    apply Nat.mul_left_cancel (n := firstCoefficient)
    · exact first.positive
    exact heq
  exact ⟨hcoefficient, two_pow_injective hpowers, hbit⟩

end ThreeNPlusMinusOne
