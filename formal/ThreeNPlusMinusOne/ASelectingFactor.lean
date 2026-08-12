import ThreeNPlusMinusOne.TransferBound

set_option autoImplicit false

/-!
# The A-selecting obligation and its bounded factor escape (Section 28)
-/

namespace ThreeNPlusMinusOne

/-- The canonical source of the side child of an A-selecting lift is below
the globally minimum source whenever `x < 2s`. -/
theorem selectedLift_side_source_strict
    {minimum source side rho : Nat}
    (_minimumPositive : 0 < minimum) (sourceBound : source < 2 * minimum)
    (sideEquation :
      side = B (Q (embeddedValue source) 1
        (sourceASelectingBit source)))
    (coordinates : StateHasSource side rho) :
    rho < minimum := by
  obtain ⟨sourceExponent, tailExponent, tailBit, coefficient,
    tail, sourceData⟩ := coordinates
  have coefficientBound := tail.coefficient_le_half
  have embeddedBound := sourceData.embedded_le_coefficient
  rw [embeddedValue_formula] at embeddedBound
  have sideChild := selectedLift_side_child source
  have sideUpper : side ≤ A (A source) := by
    rw [sideEquation]
    rcases sideChild with sideA | sideB
    · rw [sideA]
      exact Nat.le_refl _
    · rw [sideB]
      exact B_le_A (A source)
  have firstA := A_double_le source
  have secondA := A_double_le (A source)
  omega

/-- If the exponent-one member of an A-selecting obligation is DRAW, the
obligation continues canonically at `A(source)` with the opposite phase. -/
theorem minimumSource_selectedLower_continues
    {minimum source : Nat} (minimumPositive : 0 < minimum)
    (minimumDraw : MinimumDrawSource minimum)
    (sourceBound : source < 2 * minimum)
    (lowerDraw : Draw (Q (embeddedValue source) 1
      (sourceASelectingBit source))) :
    DrawObligation (A source) (1 - sourceASelectingBit source) := by
  let lower := Q (embeddedValue source) 1 (sourceASelectingBit source)
  let side := B lower
  have sideNotLosing : ¬ Losing side := by
    dsimp [side]
    exact lowerDraw.children_not_losing.2
  have sidePositive : 0 < side := by
    by_cases sideZero : side = 0
    · apply False.elim
      apply sideNotLosing
      rw [sideZero]
      exact Losing.terminal
    · omega
  obtain ⟨rho, sideCoordinates⟩ := stateHasSource_exists sidePositive
  have rhoDrop := selectedLift_side_source_strict minimumPositive sourceBound
    (side := side) rfl sideCoordinates
  have sideNotDraw := minimumDraw.not_draw_of_smaller sideCoordinates rhoDrop
  have sideWinning :=
    winning_of_not_draw_and_not_losing sideNotDraw sideNotLosing
  have expandingDraw : Draw (A lower) := by
    apply lowerDraw.A_of_B_winning
    exact sideWinning
  dsimp [DrawObligation]
  left
  rw [← A_sourceLift_selected source]
  simpa [lower] using expandingDraw

/-- Outcome fingerprint in the adjacent-pair alternative of Section 28. -/
theorem minimumSource_selectedPair_fingerprint
    {minimum source parent : Nat} (minimumPositive : 0 < minimum)
    (minimumDraw : MinimumDrawSource minimum)
    (sourceBound : source < 2 * minimum)
    (parentDraw : Draw parent)
    (parentChildren :
      (A parent = Q (embeddedValue source) 2
          (sourceASelectingBit source) ∧
        B parent = Q (embeddedValue source) 1
          (sourceASelectingBit source)) ∨
      (A parent = Q (embeddedValue source) 1
          (sourceASelectingBit source) ∧
        B parent = Q (embeddedValue source) 2
          (sourceASelectingBit source)))
    (lowerNotDraw : ¬ Draw (Q (embeddedValue source) 1
      (sourceASelectingBit source))) :
    let lower := Q (embeddedValue source) 1
      (sourceASelectingBit source)
    let upper := Q (embeddedValue source) 2
      (sourceASelectingBit source)
    let side := B lower
    let selected := A lower
    let factor := A upper
    Winning lower ∧ Draw upper ∧ Winning side ∧
      Losing selected ∧ Draw factor := by
  dsimp only
  let lower := Q (embeddedValue source) 1
    (sourceASelectingBit source)
  let upper := Q (embeddedValue source) 2
    (sourceASelectingBit source)
  let side := B lower
  let selected := A lower
  let factor := A upper
  have lowerNotLosing : ¬ Losing lower := by
    rcases parentChildren with order | order
    · have lowerEquation : B parent = lower := by
        simpa [lower] using order.2
      rw [← lowerEquation]
      exact parentDraw.children_not_losing.2
    · have lowerEquation : A parent = lower := by
        simpa [lower] using order.1
      rw [← lowerEquation]
      exact parentDraw.children_not_losing.1
  have upperNotLosing : ¬ Losing upper := by
    rcases parentChildren with order | order
    · have upperEquation : A parent = upper := by
        simpa [upper] using order.1
      rw [← upperEquation]
      exact parentDraw.children_not_losing.1
    · have upperEquation : B parent = upper := by
        simpa [upper] using order.2
      rw [← upperEquation]
      exact parentDraw.children_not_losing.2
  have lowerWinning := winning_of_not_draw_and_not_losing
    (by simpa [lower] using lowerNotDraw) lowerNotLosing
  have upperDraw : Draw upper := by
    classical
    by_cases upperIsDraw : Draw upper
    · exact upperIsDraw
    · have upperWinning := winning_of_not_draw_and_not_losing
        upperIsDraw upperNotLosing
      apply False.elim
      apply parentDraw.children_not_both_winning
      rcases parentChildren with order | order
      · rw [order.1, order.2]
        exact ⟨upperWinning, lowerWinning⟩
      · rw [order.1, order.2]
        exact ⟨lowerWinning, upperWinning⟩
  have upperSide : B upper = side := by
    dsimp [upper, side, lower]
    exact (B_Q_one_eq_two (embeddedValue_positive source)
      (embeddedValue_odd source) (sourceASelectingBit_is_bit source)).symm
  have sideNotLosing : ¬ Losing side := by
    rw [← upperSide]
    exact upperDraw.children_not_losing.2
  have sidePositive : 0 < side := by
    by_cases sideZero : side = 0
    · apply False.elim
      apply sideNotLosing
      rw [sideZero]
      exact Losing.terminal
    · omega
  obtain ⟨rho, sideCoordinates⟩ := stateHasSource_exists sidePositive
  have rhoDrop := selectedLift_side_source_strict minimumPositive sourceBound
    (side := side) rfl sideCoordinates
  have sideNotDraw := minimumDraw.not_draw_of_smaller sideCoordinates rhoDrop
  have sideWinning := winning_of_not_draw_and_not_losing
    sideNotDraw sideNotLosing
  have selectedLosing : Losing selected := by
    dsimp [selected]
    apply lowerWinning.A_losing_of_B_not_losing
    simpa [side] using sideNotLosing
  have factorDraw : Draw factor := by
    dsimp [factor]
    apply upperDraw.A_of_B_winning
    rw [upperSide]
    exact sideWinning
  exact ⟨lowerWinning, upperDraw, sideWinning,
    selectedLosing, factorDraw⟩

/-- Universal adjacent factor frame attached to the factor state. -/
theorem selectedFactor_adjacentFrame (source : Nat) :
    let phase := sourceASelectingBit source
    let factor := A (Q (embeddedValue source) 2 phase)
    let side := B (Q (embeddedValue source) 1 phase)
    ∃ lowerExponent,
      1 ≤ lowerExponent ∧
        A factor = Q (embeddedValue side) (lowerExponent + 1)
          (1 - phase) ∧
        B factor = Q (embeddedValue side) lowerExponent
          (1 - phase) := by
  dsimp only
  let phase := sourceASelectingBit source
  let factor := A (Q (embeddedValue source) 2 phase)
  let side := B (Q (embeddedValue source) 1 phase)
  have phaseBit : Bit phase := by
    simpa [phase] using sourceASelectingBit_is_bit source
  have factorEquation :
      factor = Q (3 * embeddedValue source) 1 phase := by
    dsimp [factor]
    simpa using A_Q (embeddedValue_positive source) phaseBit
      (by omega : 1 ≤ 2)
  obtain ⟨exponent, exponentLarge, expanding, contracting⟩ :=
    phaseMatch_high_adjacent_pair (z := source) phaseBit (by rfl)
  refine ⟨exponent - 1, by omega, ?_, ?_⟩
  · change A factor = Q (embeddedValue side) (exponent - 1 + 1)
      (1 - phase)
    rw [factorEquation]
    simpa [side, phase, show exponent - 1 + 1 = exponent by omega] using
      expanding
  · change B factor = Q (embeddedValue side) (exponent - 1)
      (1 - phase)
    rw [factorEquation]
    simpa [side, phase] using contracting

/-- If the factor-frame source itself does not drop below the minimum, its
lower exponent is at most three. -/
theorem selectedFactor_lowerExponent_le_three
    {minimum source lowerExponent : Nat}
    (_minimumPositive : 0 < minimum) (sourceBound : source < 2 * minimum)
    (sideSurvives :
      minimum ≤ B (Q (embeddedValue source) 1
        (sourceASelectingBit source)))
    (frame :
      A (A (Q (embeddedValue source) 2
        (sourceASelectingBit source))) =
        Q (embeddedValue (B (Q (embeddedValue source) 1
          (sourceASelectingBit source)))) (lowerExponent + 1)
          (1 - sourceASelectingBit source)) :
    lowerExponent ≤ 3 := by
  by_cases exponentSmall : lowerExponent ≤ 3
  · exact exponentSmall
  · have lowerHigh : 4 ≤ lowerExponent := by omega
    have phaseData := sourceASelectingBit_is_bit source
    have phaseBit : Bit (sourceASelectingBit source) := phaseData
    have upperEquation :
      A (A (Q (embeddedValue source) 2
        (sourceASelectingBit source))) =
        Q (9 * embeddedValue source) 0
          (sourceASelectingBit source) := by
      have first := A_Q (embeddedValue_positive source) phaseBit
        (by omega : 1 ≤ 2)
      have firstEquation :
          A (Q (embeddedValue source) 2
            (sourceASelectingBit source)) =
            Q (3 * embeddedValue source) 1
              (sourceASelectingBit source) := by
        simpa using first
      rw [firstEquation]
      have triplePositive : 0 < 3 * embeddedValue source :=
        Nat.mul_pos (by omega) (embeddedValue_positive source)
      simpa [show 3 * (3 * embeddedValue source) =
        9 * embeddedValue source by omega] using
        A_Q triplePositive phaseBit (by omega : 1 ≤ 1)
    have productBound :
      embeddedValue (B (Q (embeddedValue source) 1
        (sourceASelectingBit source))) * 2 ^ (lowerExponent + 1) ≤
        9 * embeddedValue source + 1 := by
      rw [upperEquation] at frame
      rcases phaseData with phaseZero | phaseOne
      · rw [phaseZero] at frame ⊢
        simp [Q] at frame ⊢
        omega
      · rw [phaseOne] at frame ⊢
        simp [Q] at frame ⊢
        have productPositive :
            0 < embeddedValue (B (Q (embeddedValue source) 1 1)) *
              2 ^ (lowerExponent + 1) :=
          Nat.mul_pos (embeddedValue_positive _) (Nat.pow_pos (by omega))
        omega
    have powerBound : 32 ≤ 2 ^ (lowerExponent + 1) := by
      have exponentBound : 5 ≤ lowerExponent + 1 := by omega
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) exponentBound
    let side := B (Q (embeddedValue source) 1
      (sourceASelectingBit source))
    have scaledPower := Nat.mul_le_mul_left (embeddedValue side) powerBound
    have embeddedLower : 3 * side + 1 ≤ embeddedValue side := by
      rw [embeddedValue_formula]
      have lower := three_value_le_two_A side
      omega
    have scaledLower := Nat.mul_le_mul_right 32 embeddedLower
    have embeddedUpper : embeddedValue source ≤ 3 * source + 2 := by
      rw [embeddedValue_formula]
      have upper := A_double_le source
      omega
    dsimp [side] at scaledPower scaledLower
    omega

private theorem constantTail_at_embedded_hasSource
    {source exponent tailBit : Nat} (exponentPositive : 1 ≤ exponent)
    (bit : Bit tailBit) :
    StateHasSource (Q (embeddedValue source) exponent tailBit) source := by
  let tail : IsConstantTail
      (Q (embeddedValue source) exponent tailBit)
      (embeddedValue source) exponent tailBit :=
    ⟨embeddedValue_positive source, embeddedValue_odd source,
      exponentPositive, bit, rfl⟩
  exact ⟨0, exponent, tailBit, embeddedValue source, tail, ⟨by simp⟩⟩

/-- The bounded factor alternative produced by an A-selecting obligation. -/
def ASelectingFactorEscape (source : Nat) : Prop :=
  let phase := sourceASelectingBit source
  let lower := Q (embeddedValue source) 1 phase
  let upper := Q (embeddedValue source) 2 phase
  let side := B lower
  let selected := A lower
  let factor := A upper
  ∃ lowerExponent,
    1 ≤ lowerExponent ∧ lowerExponent ≤ 3 ∧
      Winning lower ∧ Draw upper ∧ Winning side ∧
      Losing selected ∧ Draw factor ∧
      A factor = Q (embeddedValue side) (lowerExponent + 1)
        (1 - phase) ∧
      B factor = Q (embeddedValue side) lowerExponent
        (1 - phase)

/-- Complete Section 28 case split: either the canonical A-obligation
continues, or the fully marked factor escape has one of the three bounded
adjacent exponents. -/
theorem minimumSource_ASelecting_obligation_cases
    {minimum source : Nat} (minimumPositive : 0 < minimum)
    (minimumDraw : MinimumDrawSource minimum)
    (sourceBound : source < 2 * minimum)
    (obligation :
      DrawObligation source (sourceASelectingBit source)) :
    DrawObligation (A source) (1 - sourceASelectingBit source) ∨
      ASelectingFactorEscape source := by
  let phase := sourceASelectingBit source
  let lower := Q (embeddedValue source) 1 phase
  let upper := Q (embeddedValue source) 2 phase
  let side := B lower
  let selected := A lower
  let factor := A upper
  dsimp [DrawObligation] at obligation
  rcases obligation with lowerDraw | parentEntry
  · left
    exact minimumSource_selectedLower_continues minimumPositive minimumDraw
      sourceBound (by simpa [lower, phase] using lowerDraw)
  · rcases parentEntry with ⟨parent, parentDraw, parentChildren⟩
    by_cases lowerDraw : Draw lower
    · left
      exact minimumSource_selectedLower_continues minimumPositive minimumDraw
        sourceBound (by simpa [lower, phase] using lowerDraw)
    · right
      have fingerprint := minimumSource_selectedPair_fingerprint
        minimumPositive minimumDraw sourceBound parentDraw
        (by simpa [lower, upper, phase] using parentChildren)
        (by simpa [lower, phase] using lowerDraw)
      dsimp only at fingerprint
      obtain ⟨lowerExponent, exponentPositive, expanding, contracting⟩ :=
        selectedFactor_adjacentFrame source
      have complementBit : Bit (1 - phase) := by
        have phaseData : Bit phase := by
          simpa [phase] using sourceASelectingBit_is_bit source
        rcases phaseData with phaseZero | phaseOne
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      have sideSurvives : minimum ≤ side := by
        obtain ⟨child, move, childDraw⟩ := fingerprint.2.2.2.2.has_draw_child
        rcases move.2 with childA | childB
        · subst child
          have coordinates := constantTail_at_embedded_hasSource
            (source := side) (exponent := lowerExponent + 1)
            (by omega) complementBit
          rw [expanding] at childDraw
          exact minimumDraw.minimum side ⟨_, childDraw, coordinates⟩
        · subst child
          have coordinates := constantTail_at_embedded_hasSource
            (source := side) (exponent := lowerExponent)
            exponentPositive complementBit
          rw [contracting] at childDraw
          exact minimumDraw.minimum side ⟨_, childDraw, coordinates⟩
      have exponentBound := selectedFactor_lowerExponent_le_three
        minimumPositive sourceBound (by simpa [side, lower, phase] using
          sideSurvives) (by simpa [factor, upper, side, lower, phase] using
            expanding)
      dsimp [ASelectingFactorEscape]
      refine ⟨lowerExponent, exponentPositive, exponentBound, ?_⟩
      simpa [lower, upper, side, selected, factor, phase] using
        ⟨fingerprint.1, fingerprint.2.1, fingerprint.2.2.1,
          fingerprint.2.2.2.1, fingerprint.2.2.2.2,
          expanding, contracting⟩

end ThreeNPlusMinusOne
