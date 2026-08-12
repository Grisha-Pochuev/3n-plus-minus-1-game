import ThreeNPlusMinusOne.SourceBoundary

set_option autoImplicit false

/-!
# Lifted side-return source identities (Section 18)

The two theorems below identify canonical sources, not merely odd parts
observed in a bounded computation.
-/

namespace ThreeNPlusMinusOne

/-- For positive odd `w`, the canonical coefficient of `3*w` is `J(R(w))`. -/
theorem triple_odd_constantTail
    {w : Nat} (positive : 0 < w) (odd : OddNat w) :
    ∃ exponent,
      IsConstantTail (3 * w) (embeddedValue (R w)) exponent 1 := by
  have wParity : w % 2 = 1 := by
    obtain ⟨half, rfl⟩ := odd
    omega
  have remove : RemoveTwos (3 * w + 1) (embeddedValue (R w)) := by
    have core := alternatingCore_removeTwos w
    simpa [alternatingCore, wParity, embeddedValue] using core
  obtain ⟨coefficientOdd, exponent, rawEquation⟩ := remove
  have exponentPositive : 1 ≤ exponent := by
    by_cases hexponent : 1 ≤ exponent
    · exact hexponent
    · have exponentZero : exponent = 0 := by omega
      subst exponent
      simp only [Nat.pow_zero, Nat.one_mul] at rawEquation
      obtain ⟨coefficientHalf, coefficientShape⟩ := coefficientOdd
      obtain ⟨wHalf, wShape⟩ := odd
      omega
  have rawEquation' :
      3 * w + 1 = embeddedValue (R w) * 2 ^ exponent := by
    simpa [Nat.mul_comm] using rawEquation
  refine ⟨exponent, embeddedValue_positive (R w), coefficientOdd,
    exponentPositive, Or.inr rfl, ?_⟩
  unfold Q
  omega

/-- Section 18's first boxed identity, stated as uniqueness-safe source data. -/
theorem triple_odd_hasSource
    {w : Nat} (positive : 0 < w) (odd : OddNat w) :
    StateHasSource (3 * w) (R w) := by
  obtain ⟨exponent, tail⟩ := triple_odd_constantTail positive odd
  exact ⟨0, exponent, 1, embeddedValue (R w), tail, ⟨by simp⟩⟩

/--
For positive odd `w`, the canonical coefficient of `3*w-1` is
`J(R(2*w-1))`.
-/
theorem triple_odd_minus_one_constantTail
    {w : Nat} (positive : 0 < w) (odd : OddNat w) :
    ∃ exponent,
      IsConstantTail (3 * w - 1)
        (embeddedValue (R (2 * w - 1))) exponent 0 := by
  let argument := 2 * w - 1
  have argumentPositive : 0 < argument := by
    dsimp only [argument]
    omega
  have argumentOdd : OddNat argument := by
    refine ⟨w - 1, ?_⟩
    dsimp only [argument]
    omega
  have argumentParity : argument % 2 = 1 := by
    obtain ⟨half, argumentShape⟩ := argumentOdd
    rw [argumentShape]
    omega
  have doubledShape :
      alternatingCore argument = 2 * (3 * w - 1) := by
    simp [alternatingCore, argumentParity, argument]
    omega
  have doubledRemove :
      RemoveTwos (2 * (3 * w - 1))
        (embeddedValue (R argument)) := by
    rw [← doubledShape]
    simpa [embeddedValue] using alternatingCore_removeTwos argument
  have remove :
      RemoveTwos (3 * w - 1) (embeddedValue (R argument)) :=
    doubledRemove.of_double
  obtain ⟨coefficientOdd, exponent, equation⟩ := remove
  have exponentPositive : 1 ≤ exponent := by
    by_cases hexponent : 1 ≤ exponent
    · exact hexponent
    · have exponentZero : exponent = 0 := by omega
      subst exponent
      simp only [Nat.pow_zero, Nat.one_mul] at equation
      obtain ⟨coefficientHalf, coefficientShape⟩ := coefficientOdd
      obtain ⟨wHalf, wShape⟩ := odd
      omega
  refine ⟨exponent, embeddedValue_positive (R argument), coefficientOdd,
    exponentPositive, Or.inl rfl, ?_⟩
  simpa [Q, argument, Nat.mul_comm] using equation

/-- Section 18's second boxed identity as canonical source data. -/
theorem triple_odd_minus_one_hasSource
    {w : Nat} (positive : 0 < w) (odd : OddNat w) :
    StateHasSource (3 * w - 1) (R (2 * w - 1)) := by
  obtain ⟨exponent, tail⟩ :=
    triple_odd_minus_one_constantTail positive odd
  exact ⟨0, exponent, 0, embeddedValue (R (2 * w - 1)), tail,
    ⟨by simp⟩⟩

end ThreeNPlusMinusOne
