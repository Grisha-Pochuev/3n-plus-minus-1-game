import ThreeNPlusMinusOne.OppositeTail

set_option autoImplicit false

/-!
# The common-child twin recurrence (Section 30)

The bounded factor frame from Sections 28--29 consists of two adjacent
constant-tail states.  This file proves their exact common child, transfers
the DRAW outcome to that child, and records the forced LOSS alternative below
the opposite-tail WIN.  These are local consequences of a factor escape; they
do not construct the global DRAW refinement.
-/

namespace ThreeNPlusMinusOne

/-- At lower exponent one, the two adjacent frame members have the same
contracting child. -/
theorem factorFrame_commonChild_one
    {coefficient tailBit : Nat} (positive : 0 < coefficient)
    (odd : OddNat coefficient) (bit : Bit tailBit) :
    B (Q coefficient 1 tailBit) = B (Q coefficient 2 tailBit) := by
  exact B_Q_one_eq_two positive odd bit

/-- At every lower exponent at least two, expanding the lower frame member
and contracting the upper one give the same explicit constant-tail state. -/
theorem factorFrame_commonChild_long
    {coefficient lowerExponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLong : 2 ≤ lowerExponent) :
    A (Q coefficient lowerExponent tailBit) =
        Q (3 * coefficient) (lowerExponent - 1) tailBit ∧
      B (Q coefficient (lowerExponent + 1) tailBit) =
        Q (3 * coefficient) (lowerExponent - 1) tailBit := by
  constructor
  · exact A_Q positive bit (by omega)
  · simpa [show lowerExponent + 1 - 2 = lowerExponent - 1 by omega] using
      B_Q positive bit (by omega : 3 ≤ lowerExponent + 1)

/-- A DRAW parent with two named children has a DRAW member among them.  If
those two members share a child, that common child is non-losing and hence is
either WIN or DRAW. -/
theorem Draw.commonChild_of_adjacentFrame
    {parent upper lower common : Nat} (parentDraw : Draw parent)
    (upperEquation : A parent = upper) (lowerEquation : B parent = lower)
    (commonFromUpper : common = A upper ∨ common = B upper)
    (commonFromLower : common = A lower ∨ common = B lower) :
    (Draw upper ∨ Draw lower) ∧
      ¬ Losing common ∧ (Winning common ∨ Draw common) := by
  classical
  obtain ⟨next, move, nextDraw⟩ := parentDraw.has_draw_child
  have frameDraw : Draw upper ∨ Draw lower := by
    rcases move.2 with nextUpper | nextLower
    · left
      subst next
      simpa [upperEquation] using nextDraw
    · right
      subst next
      simpa [lowerEquation] using nextDraw
  have commonNotLosing : ¬ Losing common := by
    rcases frameDraw with upperDraw | lowerDraw
    · rcases commonFromUpper with commonA | commonB
      · rw [commonA]
        exact upperDraw.children_not_losing.1
      · rw [commonB]
        exact upperDraw.children_not_losing.2
    · rcases commonFromLower with commonA | commonB
      · rw [commonA]
        exact lowerDraw.children_not_losing.1
      · rw [commonB]
        exact lowerDraw.children_not_losing.2
  have commonOutcome : Winning common ∨ Draw common := by
    by_cases commonDraw : Draw common
    · exact Or.inr commonDraw
    · exact Or.inl
        (winning_of_not_draw_and_not_losing commonDraw commonNotLosing)
  exact ⟨frameDraw, commonNotLosing, commonOutcome⟩

/-- Exact Section 30 payload exported by a Section 28 factor escape. -/
def FactorTwinRecurrence (source : Nat) : Prop :=
  let phase := sourceASelectingBit source
  let oppositePhase := 1 - phase
  let lower := Q (embeddedValue source) 1 phase
  let upper := Q (embeddedValue source) 2 phase
  let side := B lower
  let coefficient := embeddedValue side
  let retained := A lower
  let factor := A upper
  ∃ lowerExponent common,
    let opposite := Q coefficient lowerExponent phase
    let high := Q coefficient (lowerExponent + 1) oppositePhase
    let low := Q coefficient lowerExponent oppositePhase
    1 ≤ lowerExponent ∧ lowerExponent ≤ 3 ∧
      Losing retained ∧ Winning opposite ∧ Winning (B retained) ∧
      Draw factor ∧ A factor = high ∧ B factor = low ∧
      A retained = opposite ∧
      ¬ Losing high ∧ ¬ Losing low ∧
      (Draw high ∨ Draw low) ∧
      ((lowerExponent = 1 ∧ common = B low ∧ common = B high) ∨
        (2 ≤ lowerExponent ∧ common = A low ∧ common = B high ∧
          common = Q (3 * coefficient) (lowerExponent - 1)
            oppositePhase ∧
          A opposite = Q (3 * coefficient) (lowerExponent - 1) phase)) ∧
      ¬ Losing common ∧ (Winning common ∨ Draw common) ∧
      (Losing (A opposite) ∨ Losing (B opposite)) ∧
      (lowerExponent = 3 →
        Losing (Q (3 * coefficient) 2 phase) ∨
          Losing (Q (3 * coefficient) 1 phase))

/-- Every bounded factor escape satisfies the complete local recurrence of
Section 30. -/
theorem ASelectingFactorEscape.twinRecurrence
    {source : Nat} (escape : ASelectingFactorEscape source) :
    FactorTwinRecurrence source := by
  classical
  have switch := escape.oppositeTailSwitch
  dsimp only at switch
  obtain ⟨lowerExponent, exponentPositive, exponentBound,
    retainedLosing, oppositeWinning, lowNotLosing, factorDraw,
    highEquation, lowEquation, oppositeEquation⟩ := switch
  let phase := sourceASelectingBit source
  let oppositePhase := 1 - phase
  let lower := Q (embeddedValue source) 1 phase
  let upper := Q (embeddedValue source) 2 phase
  let side := B lower
  let coefficient := embeddedValue side
  let retained := A lower
  let factor := A upper
  let opposite := Q coefficient lowerExponent phase
  let high := Q coefficient (lowerExponent + 1) oppositePhase
  let low := Q coefficient lowerExponent oppositePhase
  have phaseBit : Bit phase := by
    simpa [phase] using sourceASelectingBit_is_bit source
  have oppositePhaseBit : Bit oppositePhase := by
    rcases phaseBit with phaseZero | phaseOne
    · right
      simp [oppositePhase, phaseZero]
    · left
      simp [oppositePhase, phaseOne]
  have coefficientPositive : 0 < coefficient := by
    simpa [coefficient, side] using embeddedValue_positive side
  have coefficientOdd : OddNat coefficient := by
    simpa [coefficient] using embeddedValue_odd side
  have retainedPositive : 0 < retained := by
    have lowerPositive : 0 < lower := by
      rcases phaseBit with phaseZero | phaseOne
      · simp [lower, phaseZero, Q]
        exact embeddedValue_positive source
      · simp [lower, phaseOne, Q]
        have sourcePositive := embeddedValue_positive source
        omega
    exact A_pos lowerPositive
  have retainedChildren := retainedLosing.children_winning retainedPositive
  have retainedOtherWinning : Winning (B retained) := by
    simpa [retained, lower, phase] using retainedChildren.2
  have highNotLosing : ¬ Losing high := by
    have childNotLosing := factorDraw.children_not_losing.1
    rw [highEquation] at childNotLosing
    simpa [high, coefficient, side, lower, oppositePhase, phase] using
      childNotLosing
  have lowNotLosing' : ¬ Losing low := by
    simpa [low, coefficient, side, lower, oppositePhase, phase] using
      lowNotLosing
  have factorHasDraw : Draw high ∨ Draw low := by
    obtain ⟨next, move, nextDraw⟩ := factorDraw.has_draw_child
    rcases move.2 with nextHigh | nextLow
    · left
      subst next
      rw [highEquation] at nextDraw
      exact nextDraw
    · right
      subst next
      rw [lowEquation] at nextDraw
      exact nextDraw
  have oppositeChildLoss : Losing (A opposite) ∨ Losing (B opposite) := by
    by_cases expandingLoss : Losing (A opposite)
    · exact Or.inl expandingLoss
    · exact Or.inr (oppositeWinning.B_losing_of_A_not_losing expandingLoss)
  by_cases exponentOne : lowerExponent = 1
  · subst lowerExponent
    let common := B low
    have shared : B low = B high := by
      simpa [low, high, coefficient, oppositePhase] using
        factorFrame_commonChild_one coefficientPositive coefficientOdd
          oppositePhaseBit
    have commonPayload := factorDraw.commonChild_of_adjacentFrame
      (upper := high) (lower := low) (common := common)
      (by simpa [factor, upper, phase, high, coefficient, side, lower,
        oppositePhase] using highEquation)
      (by simpa [factor, upper, phase, low, coefficient, side, lower,
        oppositePhase] using lowEquation)
      (Or.inr (by simpa [common] using shared)) (Or.inr rfl)
    dsimp [FactorTwinRecurrence]
    refine ⟨1, common, ?_⟩
    refine ⟨by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [retained, lower, phase] using retainedLosing
    · simpa [opposite, coefficient, side, lower, phase] using oppositeWinning
    · exact retainedOtherWinning
    · simpa [factor, upper, phase] using factorDraw
    · simpa [factor, high, upper, coefficient, side, lower, oppositePhase,
        phase] using highEquation
    · simpa [factor, low, upper, coefficient, side, lower, oppositePhase,
        phase] using lowEquation
    · simpa [retained, opposite, lower, coefficient, side, phase] using
        oppositeEquation
    · exact highNotLosing
    · exact lowNotLosing'
    · exact factorHasDraw
    · exact Or.inl ⟨rfl, rfl, shared⟩
    · exact commonPayload.2.1
    · exact commonPayload.2.2
    · simpa [opposite, coefficient, side, lower, phase] using
        oppositeChildLoss
    · intro impossible
      omega
  · have exponentLong : 2 ≤ lowerExponent := by omega
    let common := Q (3 * coefficient) (lowerExponent - 1) oppositePhase
    have commonEquations := factorFrame_commonChild_long coefficientPositive
      oppositePhaseBit exponentLong
    have oppositeExpanding :
        A opposite = Q (3 * coefficient) (lowerExponent - 1) phase := by
      simpa [opposite] using
        A_Q coefficientPositive phaseBit (by omega : 1 ≤ lowerExponent)
    have commonPayload := factorDraw.commonChild_of_adjacentFrame
      (upper := high) (lower := low) (common := common)
      (by simpa [factor, upper, phase, high, coefficient, side, lower,
        oppositePhase] using highEquation)
      (by simpa [factor, upper, phase, low, coefficient, side, lower,
        oppositePhase] using lowEquation)
      (Or.inr (by simpa [common, high, low] using commonEquations.2.symm))
      (Or.inl (by simpa [common, low] using commonEquations.1.symm))
    have exponentThreeLoss : lowerExponent = 3 →
        Losing (Q (3 * coefficient) 2 phase) ∨
          Losing (Q (3 * coefficient) 1 phase) := by
      intro exponentThree
      subst lowerExponent
      have expandingEquation :
          A (Q coefficient 3 phase) = Q (3 * coefficient) 2 phase := by
        simpa using A_Q coefficientPositive phaseBit (by omega : 1 ≤ 3)
      have contractingEquation :
          B (Q coefficient 3 phase) = Q (3 * coefficient) 1 phase := by
        simpa using B_Q coefficientPositive phaseBit (by omega : 3 ≤ 3)
      simpa [opposite, expandingEquation, contractingEquation] using
        oppositeChildLoss
    dsimp [FactorTwinRecurrence]
    refine ⟨lowerExponent, common, ?_⟩
    refine ⟨exponentPositive, exponentBound, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [retained, lower, phase] using retainedLosing
    · simpa [opposite, coefficient, side, lower, phase] using oppositeWinning
    · exact retainedOtherWinning
    · simpa [factor, upper, phase] using factorDraw
    · simpa [factor, high, upper, coefficient, side, lower, oppositePhase,
        phase] using highEquation
    · simpa [factor, low, upper, coefficient, side, lower, oppositePhase,
        phase] using lowEquation
    · simpa [retained, opposite, lower, coefficient, side, phase] using
        oppositeEquation
    · exact highNotLosing
    · exact lowNotLosing'
    · exact factorHasDraw
    · exact Or.inr ⟨exponentLong, commonEquations.1.symm,
        commonEquations.2.symm, rfl, oppositeExpanding⟩
    · exact commonPayload.2.1
    · exact commonPayload.2.2
    · simpa [opposite, coefficient, side, lower, phase] using
        oppositeChildLoss
    · exact exponentThreeLoss

end ThreeNPlusMinusOne
