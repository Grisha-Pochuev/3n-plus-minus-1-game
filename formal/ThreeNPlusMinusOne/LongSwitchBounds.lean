import ThreeNPlusMinusOne.SignedBoundary

set_option autoImplicit false

/-!
# Finite signed valuations after the long switches (Section 32)

This file isolates the universal arithmetic and outcome lemmas used by the
exponent-two and exponent-three branches.  In particular, it turns an exact
signed valuation into canonical sources for both children of the signed
state, then proves the three finite valuation bounds of Section 32.
-/

namespace ThreeNPlusMinusOne

/-- An exact signed numerator factorization is exactly a constant-tail
description of the expanding child. -/
theorem signedTransition_tail
    {coefficient returnedCoefficient exponent tailBit : Nat}
    (coefficientPositive : 0 < coefficient)
    (returnedPositive : 0 < returnedCoefficient)
    (returnedOdd : OddNat returnedCoefficient) (bit : Bit tailBit)
    (exponentLarge : 2 ≤ exponent)
    (valuation :
      3 * coefficient + 1 - 2 * tailBit =
        2 ^ exponent * returnedCoefficient) :
    IsConstantTail (A (Q coefficient 1 tailBit)) returnedCoefficient
      exponent (1 - tailBit) := by
  have complementBit : Bit (1 - tailBit) := by
    rcases bit with bitZero | bitOne
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  refine ⟨returnedPositive, returnedOdd, by omega, complementBit, ?_⟩
  have expanded := A_Q coefficientPositive bit (by omega : 1 ≤ 1)
  rw [expanded]
  rcases bit with bitZero | bitOne
  · rw [bitZero] at valuation ⊢
    simp [Q, Nat.mul_comm] at valuation ⊢
    omega
  · rw [bitOne] at valuation ⊢
    simp [Q, Nat.mul_comm] at valuation ⊢
    have productPositive : 0 < 2 ^ exponent * returnedCoefficient :=
      Nat.mul_pos (Nat.pow_pos (by omega)) returnedPositive
    omega

/-- If the expanding child of a state has a signed valuation at least two,
both legal children have the same canonical coefficient source. -/
theorem signedTransition_children_haveSource
    {state returned exponent tailBit : Nat} (exponentLarge : 2 ≤ exponent)
    (tail : IsConstantTail (A state) (embeddedValue returned)
      exponent tailBit) :
    StateHasSource (A state) returned ∧
      StateHasSource (B state) returned := by
  have expandingSource : StateHasSource (A state) returned :=
    ⟨0, exponent, tailBit, embeddedValue returned, tail, ⟨by simp⟩⟩
  have contractingEquation :
      B state = Q (embeddedValue returned) (exponent - 1) tailBit := by
    unfold B
    rw [tail.equation]
    exact R_Q tail.positive tail.bit exponentLarge
  have contractingTail : IsConstantTail (B state)
      (embeddedValue returned) (exponent - 1) tailBit :=
    ⟨tail.positive, tail.odd, by omega, tail.bit, contractingEquation⟩
  have contractingSource : StateHasSource (B state) returned :=
    ⟨0, exponent - 1, tailBit, embeddedValue returned,
      contractingTail, ⟨by simp⟩⟩
  exact ⟨expandingSource, contractingSource⟩

/-- A DRAW state whose two signed children share a canonical source cannot
send that source below the global minimum DRAW source. -/
theorem Draw.signedTransition_source_survives
    {minimum state returned exponent tailBit : Nat}
    (stateDraw : Draw state) (minimumDraw : MinimumDrawSource minimum)
    (exponentLarge : 2 ≤ exponent)
    (tail : IsConstantTail (A state) (embeddedValue returned)
      exponent tailBit) :
    minimum ≤ returned := by
  have childSources :=
    signedTransition_children_haveSource exponentLarge tail
  by_contra sourceDrops
  have returnedSmaller : returned < minimum := by omega
  have expandingNotDraw := minimumDraw.not_draw_of_smaller
    childSources.1 returnedSmaller
  have contractingNotDraw := minimumDraw.not_draw_of_smaller
    childSources.2 returnedSmaller
  have expandingWinning := winning_of_not_draw_and_not_losing
    expandingNotDraw stateDraw.children_not_losing.1
  have contractingWinning := winning_of_not_draw_and_not_losing
    contractingNotDraw stateDraw.children_not_losing.2
  exact stateDraw.2
    (Losing.replies stateDraw.positive expandingWinning contractingWinning)

/-- The source estimate attached to a lower exponent-two factor frame. -/
theorem exponentTwo_factorSource_bound
    {source side : Nat}
    (frame :
      A (A (Q (embeddedValue source) 2
        (sourceASelectingBit source))) =
        Q (embeddedValue side) 3
          (1 - sourceASelectingBit source)) :
    24 * side ≤ 27 * source + 11 := by
  have phaseData := sourceASelectingBit_is_bit source
  have phaseBit : Bit (sourceASelectingBit source) := phaseData
  have upperEquation :
      A (A (Q (embeddedValue source) 2
        (sourceASelectingBit source))) =
        Q (9 * embeddedValue source) 0
          (sourceASelectingBit source) := by
    have first := A_Q (embeddedValue_positive source) phaseBit
      (by omega : 1 ≤ 2)
    rw [first]
    simpa [show 3 * (3 * embeddedValue source) =
      9 * embeddedValue source by omega] using
      A_Q (by omega : 0 < 3 * embeddedValue source) phaseBit
        (by omega : 1 ≤ 1)
  rw [upperEquation] at frame
  rw [embeddedValue_formula source, embeddedValue_formula side] at frame ⊢
  rcases phaseData with phaseZero | phaseOne
  · rw [phaseZero] at frame
    simp [Q] at frame
    omega
  · rw [phaseOne] at frame
    simp [Q] at frame
    omega

/-- The sharper source estimate attached to a lower exponent-three frame. -/
theorem exponentThree_factorSource_bound
    {source side : Nat}
    (frame :
      A (A (Q (embeddedValue source) 2
        (sourceASelectingBit source))) =
        Q (embeddedValue side) 4
          (1 - sourceASelectingBit source)) :
    48 * side ≤ 27 * source + 3 := by
  have phaseData := sourceASelectingBit_is_bit source
  have phaseBit : Bit (sourceASelectingBit source) := phaseData
  have upperEquation :
      A (A (Q (embeddedValue source) 2
        (sourceASelectingBit source))) =
        Q (9 * embeddedValue source) 0
          (sourceASelectingBit source) := by
    have first := A_Q (embeddedValue_positive source) phaseBit
      (by omega : 1 ≤ 2)
    rw [first]
    simpa [show 3 * (3 * embeddedValue source) =
      9 * embeddedValue source by omega] using
      A_Q (by omega : 0 < 3 * embeddedValue source) phaseBit
        (by omega : 1 ≤ 1)
  rw [upperEquation] at frame
  rw [embeddedValue_formula source, embeddedValue_formula side] at frame ⊢
  rcases phaseData with phaseZero | phaseOne
  · rw [phaseZero] at frame
    simp [Q] at frame
    omega
  · rw [phaseOne] at frame
    simp [Q] at frame
    omega

/-- The first signed valuation after a lower exponent-two switch is at most
four whenever its returned source survives the global minimum. -/
theorem exponentTwo_signedValuation_le_four
    {minimum source side returned exponent tailBit : Nat}
    (minimumPositive : 0 < minimum) (sourceBound : source < 2 * minimum)
    (sideBound : 24 * side ≤ 27 * source + 11)
    (bit : Bit tailBit) (returnedSurvives : minimum ≤ returned)
    (valuation :
      9 * embeddedValue side + 1 - 2 * tailBit =
        2 ^ exponent * embeddedValue returned) :
    exponent ≤ 4 := by
  by_contra exponentHigh
  have powerBound : 32 ≤ 2 ^ exponent := by
    have five : 5 ≤ exponent := by omega
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) five
  have scaledPower := Nat.mul_le_mul_right
    (embeddedValue returned) powerBound
  rw [← valuation] at scaledPower
  rw [embeddedValue_formula returned, embeddedValue_formula side]
    at scaledPower
  rcases bit with bitZero | bitOne
  · rw [bitZero] at scaledPower
    omega
  · rw [bitOne] at scaledPower
    omega

/-- The contracting signed continuation after a lower exponent-three switch
has valuation at most three. -/
theorem exponentThree_firstValuation_le_three
    {minimum source side returned exponent tailBit : Nat}
    (minimumPositive : 0 < minimum) (sourceBound : source < 2 * minimum)
    (sideBound : 48 * side ≤ 27 * source + 3)
    (bit : Bit tailBit) (returnedSurvives : minimum ≤ returned)
    (valuation :
      9 * embeddedValue side + 1 - 2 * tailBit =
        2 ^ exponent * embeddedValue returned) :
    exponent ≤ 3 := by
  by_contra exponentHigh
  have powerBound : 16 ≤ 2 ^ exponent := by
    have four : 4 ≤ exponent := by omega
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) four
  have scaledPower := Nat.mul_le_mul_right
    (embeddedValue returned) powerBound
  rw [← valuation] at scaledPower
  rw [embeddedValue_formula returned, embeddedValue_formula side]
    at scaledPower
  rcases bit with bitZero | bitOne
  · rw [bitZero] at scaledPower
    omega
  · rw [bitOne] at scaledPower
    omega

/-- If the other exponent-three child is DRAW, its next signed valuation is
at most four. -/
theorem exponentThree_secondValuation_le_four
    {minimum source side returned exponent tailBit : Nat}
    (minimumPositive : 0 < minimum) (sourceBound : source < 2 * minimum)
    (sideBound : 48 * side ≤ 27 * source + 3)
    (bit : Bit tailBit) (returnedSurvives : minimum ≤ returned)
    (valuation :
      27 * embeddedValue side + 1 - 2 * tailBit =
        2 ^ exponent * embeddedValue returned) :
    exponent ≤ 4 := by
  by_contra exponentHigh
  have powerBound : 32 ≤ 2 ^ exponent := by
    have five : 5 ≤ exponent := by omega
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) five
  have scaledPower := Nat.mul_le_mul_right
    (embeddedValue returned) powerBound
  rw [← valuation] at scaledPower
  rw [embeddedValue_formula returned, embeddedValue_formula side]
    at scaledPower
  rcases bit with bitZero | bitOne
  · rw [bitZero] at scaledPower
    omega
  · rw [bitOne] at scaledPower
    omega

end ThreeNPlusMinusOne
