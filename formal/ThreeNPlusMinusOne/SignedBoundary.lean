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

end ThreeNPlusMinusOne
