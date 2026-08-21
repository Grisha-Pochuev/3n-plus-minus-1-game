import ThreeNPlusMinusOne.TwinRecurrence

set_option autoImplicit false

/-!
# The exponent-one signed boundary (Section 31)

This file begins the Section 31 rank analysis.  It proves that an
exponent-one factor frame can only use the A-selecting phase at the retained
source, so the factor-frame source is exactly `A (A source)`.
-/

namespace ThreeNPlusMinusOne

/-- If the bounded factor frame has lower exponent one, its ordinary source
is exactly the twice-expanded source from which the A-selecting obligation
started. -/
theorem selectedFactor_exponentOne_side_eq_AA
    {source : Nat}
    (expandingFrame :
      A (A (Q (embeddedValue source) 2
        (sourceASelectingBit source))) =
        Q (embeddedValue (B (Q (embeddedValue source) 1
          (sourceASelectingBit source)))) 2
          (1 - sourceASelectingBit source)) :
    B (Q (embeddedValue source) 1 (sourceASelectingBit source)) =
      A (A source) := by
  let phase := sourceASelectingBit source
  let oppositePhase := 1 - phase
  let lower := Q (embeddedValue source) 1 phase
  let side := B lower
  have phaseBit : Bit phase := by
    simpa [phase] using sourceASelectingBit_is_bit source
  have oppositePhaseBit : Bit oppositePhase := by
    rcases phaseBit with phaseZero | phaseOne
    · right
      simp [oppositePhase, phaseZero]
    · left
      simp [oppositePhase, phaseOne]
  have nextBit : Bit (sourceASelectingBit (A source)) :=
    sourceASelectingBit_is_bit (A source)
  have retainedEquation :
      A lower = Q (embeddedValue (A source)) 1 oppositePhase := by
    simpa [lower, phase, oppositePhase] using A_sourceLift_selected source
  have oppositeEquation :
      A (A lower) = Q (embeddedValue side) 1 phase := by
    simpa [lower, side, phase, oppositePhase] using
      selectedFactor_oppositeTwin (lowerExponent := 1) expandingFrame
  by_cases selecting :
      oppositePhase = sourceASelectingBit (A source)
  · have phaseComplement :
        phase = 1 - sourceASelectingBit (A source) := by
      rcases phaseBit with phaseValue | phaseValue <;>
        rcases nextBit with nextValue | nextValue <;> omega
    have secondSelected := A_sourceLift_selected (A source)
    have stateEquation :
        Q (embeddedValue (A (A source))) 1 phase =
          Q (embeddedValue side) 1 phase := by
      calc
        Q (embeddedValue (A (A source))) 1 phase =
            Q (embeddedValue (A (A source))) 1
              (1 - sourceASelectingBit (A source)) := by
                rw [phaseComplement]
        _ = A (Q (embeddedValue (A source)) 1
              (sourceASelectingBit (A source))) := secondSelected.symm
        _ = A (Q (embeddedValue (A source)) 1 oppositePhase) := by
              rw [selecting]
        _ = A (A lower) := by rw [retainedEquation]
        _ = Q (embeddedValue side) 1 phase := oppositeEquation
    let firstTail : IsConstantTail
        (Q (embeddedValue (A (A source))) 1 phase)
        (embeddedValue (A (A source))) 1 phase :=
      ⟨embeddedValue_positive _, embeddedValue_odd _, by omega,
        phaseBit, rfl⟩
    let secondTail : IsConstantTail
        (Q (embeddedValue (A (A source))) 1 phase)
        (embeddedValue side) 1 phase :=
      ⟨embeddedValue_positive _, embeddedValue_odd _, by omega,
        phaseBit, stateEquation⟩
    have coefficientEquation := (firstTail.unique secondTail).1
    exact (embeddedValue_injective coefficientEquation).symm
  · have nonselecting :
        oppositePhase = 1 - sourceASelectingBit (A source) := by
      rcases oppositePhaseBit with oppositeValue | oppositeValue <;>
        rcases nextBit with nextValue | nextValue <;> omega
    obtain ⟨exponent, exponentLarge, nonselectedTail⟩ :=
      sourceLift_nonselected_constantTail (A source)
    have liftedTail : IsConstantTail
        (A (A lower)) (embeddedValue (B (A source))) exponent
          (sourceASelectingBit (A source)) := by
      rw [retainedEquation, nonselecting]
      exact nonselectedTail
    let exponentOneTail : IsConstantTail
        (A (A lower)) (embeddedValue side) 1 phase :=
      ⟨embeddedValue_positive _, embeddedValue_odd _, by omega,
        phaseBit, oppositeEquation⟩
    have exponentEquation := (liftedTail.unique exponentOneTail).2.1
    omega

/-- In the A-selecting signed continuation of the exponent-one frame, the
canonical source of the common child is strictly smaller than the source
which generated the factor fork. -/
theorem exponentOne_commonChild_source_strict
    {source side common rho : Nat} (sourceLarge : 4 ≤ source)
    (sideEquation : side = A (A source))
    (phaseEquation :
      1 - sourceASelectingBit source = sourceASelectingBit side)
    (commonEquation :
      common = B (Q (embeddedValue side) 1
        (1 - sourceASelectingBit source)))
    (coordinates : StateHasSource common rho) :
    rho < source := by
  have commonChild : common = A (A side) ∨ common = B (A side) := by
    rw [commonEquation, phaseEquation]
    exact selectedLift_side_child side
  have commonBound : common ≤ A (A side) := by
    rcases commonChild with commonA | commonB
    · rw [commonA]
      exact Nat.le_refl _
    · rw [commonB]
      exact B_le_A (A side)
  obtain ⟨sourceExponent, tailExponent, tailBit, coefficient,
    tail, sourceData⟩ := coordinates
  have coefficientBound := tail.coefficient_le_half
  have embeddedBound := sourceData.embedded_le_coefficient
  rw [embeddedValue_formula] at embeddedBound
  have firstExpansion := A_double_le source
  have secondExpansion := A_double_le (A source)
  have thirdExpansion := A_double_le side
  have fourthExpansion := A_double_le (A side)
  rw [sideEquation] at commonBound thirdExpansion fourthExpansion
  omega

/-- The exact signed valuation controls the selected B-source with its full
power of two, rather than only through a fixed valuation cutoff. -/
theorem pow_two_B_le_of_nonselected
    {source exponent : Nat} (exponentLarge : 2 ≤ exponent)
    (tail : IsConstantTail
      (A (Q (embeddedValue source) 1
        (1 - sourceASelectingBit source)))
      (embeddedValue (B source)) exponent
      (sourceASelectingBit source)) :
    2 ^ exponent * B source ≤ 3 * source + 1 := by
  have phaseData := sourceASelectingBit_is_bit source
  have complementBit : Bit (1 - sourceASelectingBit source) := by
    rcases phaseData with phaseZero | phaseOne
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have expanded := A_Q (embeddedValue_positive source) complementBit
    (by omega : 1 ≤ 1)
  have expandedValue :
      A (Q (embeddedValue source) 1
        (1 - sourceASelectingBit source)) =
        3 * embeddedValue source -
          (1 - sourceASelectingBit source) := by
    simpa [Q] using expanded
  have productBound :
      2 ^ exponent * embeddedValue (B source) ≤
        3 * embeddedValue source + 1 := by
    have equation := tail.equation
    rw [expandedValue] at equation
    unfold Q at equation
    rcases phaseData with phaseZero | phaseOne
    · rw [phaseZero] at equation
      simp at equation
      rw [Nat.mul_comm]
      omega
    · rw [phaseOne] at equation
      simp at equation
      have productPositive :
          0 < embeddedValue (B source) * 2 ^ exponent :=
        Nat.mul_pos (embeddedValue_positive (B source))
          (Nat.pow_pos (by omega))
      rw [Nat.mul_comm]
      omega
  have powerAtLeastFour : 4 ≤ 2 ^ exponent := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) exponentLarge
  have embeddedLower :
      3 * B source + 1 ≤ embeddedValue (B source) := by
    rw [embeddedValue_formula]
    have lower := three_value_le_two_A (B source)
    omega
  have embeddedUpper : embeddedValue source ≤ 3 * source + 2 := by
    rw [embeddedValue_formula]
    have upper := A_double_le source
    omega
  have scaledLower := Nat.mul_le_mul_left (2 ^ exponent) embeddedLower
  omega

/-- The B-selecting half of the exponent-one boundary has the exact source
`B(side)` and the finite valuation trichotomy stated in Section 31. -/
theorem exponentOne_BSelecting_source_and_bounds
    {minimum source side common : Nat} (minimumPositive : 0 < minimum)
    (sourceBound : source < 2 * minimum)
    (sideEquation : side = A (A source))
    (phaseEquation :
      1 - sourceASelectingBit source =
        1 - sourceASelectingBit side)
    (commonEquation :
      common = B (Q (embeddedValue side) 1
        (1 - sourceASelectingBit source))) :
    ∃ exponent,
      2 ≤ exponent ∧ StateHasSource common (B side) ∧
        (4 ≤ exponent → B side < minimum) ∧
        (exponent = 3 → 16 * B side < 27 * minimum) ∧
        (exponent = 2 → 8 * B side < 27 * minimum) := by
  obtain ⟨exponent, exponentLarge, tail⟩ :=
    sourceLift_nonselected_constantTail side
  have commonSource : StateHasSource common (B side) := by
    rw [commonEquation, phaseEquation]
    exact sourceLift_nonselected_side_hasSource side
  have valuationBound :=
    pow_two_B_le_of_nonselected exponentLarge tail
  have firstExpansion := A_double_le source
  have secondExpansion := A_double_le (A source)
  have sideBound : 4 * side ≤ 9 * source + 5 := by
    rw [sideEquation]
    omega
  refine ⟨exponent, exponentLarge, commonSource, ?_, ?_, ?_⟩
  · intro exponentHigh
    have powerBound : 16 ≤ 2 ^ exponent := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) exponentHigh
    have scaledPower := Nat.mul_le_mul_right (B side) powerBound
    omega
  · intro exponentThree
    have exactBound : 8 * B side ≤ 3 * side + 1 := by
      simpa [exponentThree] using valuationBound
    omega
  · intro exponentTwo
    have exactBound : 4 * B side ≤ 3 * side + 1 := by
      simpa [exponentTwo] using valuationBound
    omega

end ThreeNPlusMinusOne
