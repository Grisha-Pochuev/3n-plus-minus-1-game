import ThreeNPlusMinusOne.ConstantTailCoordinates

set_option autoImplicit false

/-!
# Coefficient sources (Section 17)
-/

namespace ThreeNPlusMinusOne

def RemoveThrees (value remainder : Nat) : Prop :=
  remainder % 3 ≠ 0 ∧ ∃ exponent, value = 3 ^ exponent * remainder

theorem RemoveThrees.exists_of_positive {value : Nat} (positive : 0 < value) :
    ∃ remainder, RemoveThrees value remainder := by
  refine Nat.strongRecOn
    (motive := fun value => 0 < value → ∃ remainder, RemoveThrees value remainder)
    value ?_ positive
  intro value ih positive
  by_cases divisible : value % 3 = 0
  · let quotient := value / 3
    have quotientPositive : 0 < quotient := by omega
    have quotientSmaller : quotient < value := by omega
    have hvalue : value = 3 * quotient := by omega
    obtain ⟨remainder, nondivisible, exponent, hexponent⟩ :=
      ih quotient quotientSmaller quotientPositive
    refine ⟨remainder, nondivisible, exponent + 1, ?_⟩
    rw [hvalue, hexponent, Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_left_comm]
  · exact ⟨value, divisible, 0, by simp⟩

private theorem nondivisible_forces_zero_exponent
    {remainder factor exponent : Nat}
    (nondivisible : remainder % 3 ≠ 0)
    (factorization : remainder = 3 ^ exponent * factor) :
    exponent = 0 := by
  by_cases hzero : exponent = 0
  · exact hzero
  · obtain ⟨rest, hrest⟩ : ∃ rest, exponent = rest + 1 :=
      ⟨exponent - 1, by omega⟩
    apply False.elim
    apply nondivisible
    rw [factorization, hrest, Nat.pow_succ]
    have hshape : (3 ^ rest * 3) * factor = 3 * (3 ^ rest * factor) := by
      ac_rfl
    rw [hshape]
    simp

theorem RemoveThrees.unique {value first second : Nat}
    (firstDecomposition : RemoveThrees value first)
    (secondDecomposition : RemoveThrees value second) : first = second := by
  obtain ⟨firstNondivisible, firstExponent, firstEquation⟩ :=
    firstDecomposition
  obtain ⟨secondNondivisible, secondExponent, secondEquation⟩ :=
    secondDecomposition
  rcases Nat.le_total firstExponent secondExponent with hle | hle
  · obtain ⟨difference, hdifference⟩ :
        ∃ difference, secondExponent = firstExponent + difference :=
      ⟨secondExponent - firstExponent, by omega⟩
    have hcancel : first = 3 ^ difference * second := by
      apply Nat.mul_left_cancel (n := 3 ^ firstExponent)
      · exact Nat.pow_pos (by decide)
      calc
        3 ^ firstExponent * first = value := firstEquation.symm
        _ = 3 ^ secondExponent * second := secondEquation
        _ = 3 ^ firstExponent * (3 ^ difference * second) := by
          simp [hdifference, Nat.pow_add, Nat.mul_assoc]
    have hzero := nondivisible_forces_zero_exponent
      firstNondivisible hcancel
    simpa [hzero] using hcancel
  · obtain ⟨difference, hdifference⟩ :
        ∃ difference, firstExponent = secondExponent + difference :=
      ⟨firstExponent - secondExponent, by omega⟩
    have hcancel : second = 3 ^ difference * first := by
      apply Nat.mul_left_cancel (n := 3 ^ secondExponent)
      · exact Nat.pow_pos (by decide)
      calc
        3 ^ secondExponent * second = value := secondEquation.symm
        _ = 3 ^ firstExponent * first := firstEquation
        _ = 3 ^ secondExponent * (3 ^ difference * first) := by
          simp [hdifference, Nat.pow_add, Nat.mul_assoc]
    have hzero := nondivisible_forces_zero_exponent
      secondNondivisible hcancel
    simpa [hzero] using hcancel.symm

theorem OddNat.mul {first second : Nat}
    (firstOdd : OddNat first) (secondOdd : OddNat second) :
    OddNat (first * second) := by
  obtain ⟨a, rfl⟩ := firstOdd
  obtain ⟨b, rfl⟩ := secondOdd
  refine ⟨2 * a * b + a + b, ?_⟩
  simp [Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem odd_three_pow (exponent : Nat) : OddNat (3 ^ exponent) := by
  induction exponent with
  | zero => exact ⟨0, by simp⟩
  | succ exponent ih =>
      rw [Nat.pow_succ]
      exact ih.mul ⟨1, by omega⟩

theorem OddNat.right_of_mul {first second : Nat}
    (productOdd : OddNat (first * second)) (_firstOdd : OddNat first) :
    OddNat second := by
  rcases even_or_odd second with ⟨half, rfl⟩ | secondOdd
  · apply False.elim
    apply productOdd.not_even
    exact ⟨first * half, by simp [Nat.mul_assoc, Nat.mul_comm]⟩
  · exact secondOdd

/-- Remove all factors of three from an odd value and keep an odd remainder. -/
theorem RemoveThrees.exists_odd {value : Nat}
    (positive : 0 < value) (odd : OddNat value) :
    ∃ remainder exponent,
      0 < remainder ∧ OddNat remainder ∧ remainder % 3 ≠ 0 ∧
      value = 3 ^ exponent * remainder := by
  obtain ⟨remainder, nondivisible, exponent, heq⟩ :=
    RemoveThrees.exists_of_positive positive
  have remainderPositive : 0 < remainder := by
    by_cases hzero : remainder = 0
    · subst remainder
      simp at nondivisible
    · omega
  have remainderOdd : OddNat remainder := by
    rw [heq] at odd
    exact odd.right_of_mul (odd_three_pow exponent)
  exact ⟨remainder, exponent, remainderPositive, remainderOdd,
    nondivisible, heq⟩

def inverseA (value : Nat) : Nat :=
  if value % 3 = 0 then 2 * (value / 3)
  else 2 * ((value - 2) / 3) + 1

theorem A_inverseA {value : Nat} (notOne : value % 3 ≠ 1) :
    A (inverseA value) = value := by
  have residue : value % 3 = 0 ∨ value % 3 = 2 := by omega
  rcases residue with hzero | htwo
  · simp [inverseA, hzero, A_even]
    omega
  · have hnotzero : value % 3 ≠ 0 := by omega
    simp [inverseA, hnotzero, A_odd]
    omega

theorem embeddedValue_not_divisible_by_three (source : Nat) :
    embeddedValue source % 3 ≠ 0 := by
  rcases even_or_odd source with ⟨half, hsource⟩ | ⟨half, hsource⟩
  · rw [hsource, embeddedValue_even_coordinate]
    omega
  · rw [hsource, embeddedValue_odd_coordinate]
    omega

theorem A_injective {first second : Nat} (equal : A first = A second) :
    first = second := by
  rcases even_or_odd first with ⟨a, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases even_or_odd second with ⟨b, rfl⟩ | ⟨b, rfl⟩ <;>
    simp only [A_even, A_odd] at equal <;> omega

theorem embeddedValue_injective {first second : Nat}
    (equal : embeddedValue first = embeddedValue second) : first = second := by
  unfold embeddedValue at equal
  apply A_injective
  omega

/-- Every positive odd coefficient is `3^k * J(source)`. -/
theorem coefficientSource_exists {coefficient : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient) :
    ∃ source exponent,
      coefficient = 3 ^ exponent * embeddedValue source := by
  obtain ⟨remainder, exponent, remainderPositive, remainderOdd,
    nondivisible, heq⟩ := RemoveThrees.exists_odd positive odd
  obtain ⟨half, hhalf⟩ := remainderOdd
  have halfNotOne : half % 3 ≠ 1 := by
    rw [hhalf] at nondivisible
    omega
  let source := inverseA half
  have hA : A source = half := A_inverseA halfNotOne
  have hJ : embeddedValue source = remainder := by
    unfold embeddedValue
    rw [hA, hhalf]
  exact ⟨source, exponent, by rw [hJ]; exact heq⟩

structure IsCoefficientSource
    (coefficient source exponent : Nat) : Prop where
  equation : coefficient = 3 ^ exponent * embeddedValue source

theorem coefficientSource_exists_unique {coefficient : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient) :
    ∃ source exponent, IsCoefficientSource coefficient source exponent := by
  obtain ⟨source, exponent, equation⟩ :=
    coefficientSource_exists positive odd
  exact ⟨source, exponent, ⟨equation⟩⟩

private theorem three_pow_strict {lower upper : Nat} (h : lower < upper) :
    3 ^ lower < 3 ^ upper := by
  induction upper generalizing lower with
  | zero => omega
  | succ upper ih =>
      by_cases heq : lower = upper
      · subst lower
        rw [Nat.pow_succ]
        have hpositive : 0 < 3 ^ upper := Nat.pow_pos (by decide)
        omega
      · have hlower : lower < upper := by omega
        have hprevious := ih hlower
        rw [Nat.pow_succ]
        have hpositive : 0 < 3 ^ upper := Nat.pow_pos (by decide)
        omega

private theorem three_pow_injective {first second : Nat}
    (equal : 3 ^ first = 3 ^ second) : first = second := by
  rcases Nat.lt_trichotomy first second with hlt | heq | hgt
  · exact False.elim ((Nat.ne_of_lt (three_pow_strict hlt)) equal)
  · exact heq
  · exact False.elim ((Nat.ne_of_gt (three_pow_strict hgt)) equal)

/-- The source and power of three of an odd coefficient are unique. -/
theorem IsCoefficientSource.unique
    {coefficient firstSource firstExponent secondSource secondExponent : Nat}
    (first : IsCoefficientSource coefficient firstSource firstExponent)
    (second : IsCoefficientSource coefficient secondSource secondExponent) :
    firstSource = secondSource ∧ firstExponent = secondExponent := by
  have firstRemoval : RemoveThrees coefficient (embeddedValue firstSource) :=
    ⟨embeddedValue_not_divisible_by_three firstSource,
      firstExponent, first.equation⟩
  have secondRemoval : RemoveThrees coefficient (embeddedValue secondSource) :=
    ⟨embeddedValue_not_divisible_by_three secondSource,
      secondExponent, second.equation⟩
  have hvalue := RemoveThrees.unique firstRemoval secondRemoval
  have hsource : firstSource = secondSource := embeddedValue_injective hvalue
  subst secondSource
  have hpowers : 3 ^ firstExponent = 3 ^ secondExponent := by
    apply Nat.mul_left_cancel (n := embeddedValue firstSource)
    · exact embeddedValue_positive firstSource
    calc
      embeddedValue firstSource * 3 ^ firstExponent =
          3 ^ firstExponent * embeddedValue firstSource := Nat.mul_comm _ _
      _ = coefficient := first.equation.symm
      _ = 3 ^ secondExponent * embeddedValue firstSource := second.equation
      _ = embeddedValue firstSource * 3 ^ secondExponent := Nat.mul_comm _ _
  exact ⟨rfl, three_pow_injective hpowers⟩

/-- Canonical combined coordinates `Q_r^e(3^k * J(source))`. -/
def IsSourceCoordinates
    (state source sourceExponent tailExponent tailBit : Nat) : Prop :=
  ∃ coefficient,
    IsConstantTail state coefficient tailExponent tailBit ∧
    IsCoefficientSource coefficient source sourceExponent

theorem sourceCoordinates_exists {state : Nat} (positive : 0 < state) :
    ∃ source sourceExponent tailExponent tailBit,
      IsSourceCoordinates state source sourceExponent tailExponent tailBit := by
  obtain ⟨coefficient, tailExponent, tailBit, tail⟩ :=
    constantTailCoordinates_exists positive
  obtain ⟨source, sourceExponent, sourceCoordinates⟩ :=
    coefficientSource_exists_unique tail.positive tail.odd
  exact ⟨source, sourceExponent, tailExponent, tailBit,
    ⟨coefficient, tail, sourceCoordinates⟩⟩

theorem IsSourceCoordinates.unique
    {state firstSource firstSourceExponent firstTailExponent firstBit
      secondSource secondSourceExponent secondTailExponent secondBit : Nat}
    (first : IsSourceCoordinates state firstSource firstSourceExponent
      firstTailExponent firstBit)
    (second : IsSourceCoordinates state secondSource secondSourceExponent
      secondTailExponent secondBit) :
    firstSource = secondSource ∧
      firstSourceExponent = secondSourceExponent ∧
      firstTailExponent = secondTailExponent ∧ firstBit = secondBit := by
  obtain ⟨firstCoefficient, firstTail, firstSourceData⟩ := first
  obtain ⟨secondCoefficient, secondTail, secondSourceData⟩ := second
  obtain ⟨coefficientEqual, tailExponentEqual, bitEqual⟩ :=
    firstTail.unique secondTail
  subst secondCoefficient
  have sourceData := firstSourceData.unique secondSourceData
  exact ⟨sourceData.1, sourceData.2, tailExponentEqual, bitEqual⟩

theorem embeddedValue_formula (source : Nat) :
    embeddedValue source = 3 * source + 1 + source % 2 := by
  rcases even_or_odd source with ⟨half, hsource⟩ | ⟨half, hsource⟩
  · rw [hsource, embeddedValue_even_coordinate]
    omega
  · rw [hsource, embeddedValue_odd_coordinate]
    omega

theorem embeddedValue_strictMono {first second : Nat}
    (less : embeddedValue first < embeddedValue second) : first < second := by
  rw [embeddedValue_formula, embeddedValue_formula] at less
  omega

theorem IsCoefficientSource.embedded_le_coefficient
    {coefficient source exponent : Nat}
    (coordinates : IsCoefficientSource coefficient source exponent) :
    embeddedValue source ≤ coefficient := by
  rw [coordinates.equation]
  have hpower : 1 ≤ 3 ^ exponent := by
    have hpositive : 0 < 3 ^ exponent := Nat.pow_pos (by decide)
    omega
  calc
    embeddedValue source = 1 * embeddedValue source := by simp
    _ ≤ 3 ^ exponent * embeddedValue source :=
      Nat.mul_le_mul_right (embeddedValue source) hpower

/-- A coefficient below `J(source)` has a strictly smaller canonical source. -/
theorem source_strict_of_coefficient_lt
    {coefficient childSource childExponent source : Nat}
    (coordinates : IsCoefficientSource coefficient childSource childExponent)
    (less : coefficient < embeddedValue source) : childSource < source := by
  apply embeddedValue_strictMono
  exact Nat.lt_of_le_of_lt coordinates.embedded_le_coefficient less

end ThreeNPlusMinusOne
