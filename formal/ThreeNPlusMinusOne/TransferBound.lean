import ThreeNPlusMinusOne.ValuationTwoFilter

set_option autoImplicit false

/-!
# At most two further B-source transfers survive (Section 27)
-/

namespace ThreeNPlusMinusOne

/-- The two outcome-compatible entry forms denoted `O(source, phase)` in
Section 27. -/
def DrawObligation (source phase : Nat) : Prop :=
  let lower := Q (embeddedValue source) 1 phase
  let upper := Q (embeddedValue source) 2 phase
  Draw lower ∨
    ∃ parent,
      Draw parent ∧
        ((A parent = upper ∧ B parent = lower) ∨
          (A parent = lower ∧ B parent = upper))

/-- An exponent-two B-selecting transfer preserves the exact obligation
form and flips its phase. -/
theorem bSelecting_valuationTwo_obligation_transfer
    {source : Nat} (valuation : BSelectingValuationTwo source)
    (obligation :
      DrawObligation source (1 - sourceASelectingBit source)) :
    DrawObligation (B source) (sourceASelectingBit source) := by
  let phase := 1 - sourceASelectingBit source
  let lower := Q (embeddedValue source) 1 phase
  let upper := Q (embeddedValue source) 2 phase
  let newLower := Q (embeddedValue (B source)) 1
    (sourceASelectingBit source)
  let newUpper := Q (embeddedValue (B source)) 2
    (sourceASelectingBit source)
  have deepEquation : A lower = newUpper := by
    simpa [lower, newUpper, phase, BSelectingValuationTwo] using
      valuation.equation
  have sideEquation : B lower = newLower := by
    dsimp [lower, newLower]
    unfold B
    rw [valuation.equation]
    exact R_Q valuation.positive valuation.bit (by omega)
  have upperSide : B upper = newLower := by
    calc
      B upper = B lower := by
        dsimp [upper, lower, phase]
        exact (B_Q_one_eq_two (embeddedValue_positive source)
          (embeddedValue_odd source) (by
            have phaseData := sourceASelectingBit_is_bit source
            rcases phaseData with phaseZero | phaseOne
            · exact Or.inr (by omega)
            · exact Or.inl (by omega))).symm
      _ = newLower := sideEquation
  dsimp [DrawObligation] at obligation ⊢
  change Draw lower ∨
    ∃ parent, Draw parent ∧
      ((A parent = upper ∧ B parent = lower) ∨
        (A parent = lower ∧ B parent = upper)) at obligation
  change Draw newLower ∨
    ∃ parent, Draw parent ∧
      ((A parent = newUpper ∧ B parent = newLower) ∨
        (A parent = newLower ∧ B parent = newUpper))
  rcases obligation with lowerDraw | parentEntry
  · right
    refine ⟨lower, lowerDraw, Or.inl ⟨deepEquation, sideEquation⟩⟩
  · rcases parentEntry with ⟨parent, parentDraw, parentChildren⟩
    by_cases lowerDraw : Draw lower
    · right
      exact ⟨lower, lowerDraw, Or.inl ⟨deepEquation, sideEquation⟩⟩
    · have lowerNotLosing : ¬ Losing lower := by
        rcases parentChildren with order | order
        · rw [← order.2]
          exact parentDraw.children_not_losing.2
        · rw [← order.1]
          exact parentDraw.children_not_losing.1
      have upperNotLosing : ¬ Losing upper := by
        rcases parentChildren with order | order
        · rw [← order.1]
          exact parentDraw.children_not_losing.1
        · rw [← order.2]
          exact parentDraw.children_not_losing.2
      have lowerWinning :=
        winning_of_not_draw_and_not_losing lowerDraw lowerNotLosing
      have upperDraw : Draw upper := by
        classical
        by_cases upperIsDraw : Draw upper
        · exact upperIsDraw
        · have upperWinning :=
            winning_of_not_draw_and_not_losing upperIsDraw upperNotLosing
          apply False.elim
          apply parentDraw.children_not_both_winning
          rcases parentChildren with order | order
          · rw [order.1, order.2]
            exact ⟨upperWinning, lowerWinning⟩
          · rw [order.1, order.2]
            exact ⟨lowerWinning, upperWinning⟩
      have newLowerNotLosing : ¬ Losing newLower := by
        rw [← upperSide]
        exact upperDraw.children_not_losing.2
      have deepLosing : Losing (A lower) := by
        apply lowerWinning.A_losing_of_B_not_losing
        rw [sideEquation]
        exact newLowerNotLosing
      have transferred := bSelecting_draw_transfer (source := source)
        (parent := parent) (Or.inr ⟨parentDraw, parentChildren⟩)
      rcases transferred with deepDraw | sideDraw
      · apply False.elim
        apply deepDraw.2
        exact deepLosing
      · left
        rwa [sideEquation] at sideDraw

/-- Universal one-step estimate used to bound a run of valuation-two
transfers. -/
theorem four_B_le (value : Nat) : 4 * B value ≤ 3 * value + 1 := by
  have remainderBound := R_le_half (A value)
  have expandingBound := A_double_le value
  unfold B
  omega

theorem three_value_le_two_A (value : Nat) :
    3 * value ≤ 2 * A value := by
  unfold A
  omega

/-- If the exact B-selecting source valuation is at least three, two
alternating bits have been removed and the selected source obeys the sharper
one-eighth estimate. -/
theorem eight_B_le_of_high_nonselected
    {source exponent : Nat}
    (exponentHigh : 3 ≤ exponent)
    (tail : IsConstantTail
      (A (Q (embeddedValue source) 1
        (1 - sourceASelectingBit source)))
      (embeddedValue (B source)) exponent
      (sourceASelectingBit source)) :
    8 * B source ≤ 3 * source + 1 := by
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
        Nat.mul_pos (embeddedValue_positive (B source)) (Nat.pow_pos (by omega))
      rw [Nat.mul_comm]
      omega
  have powerBound : 8 ≤ 2 ^ exponent := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < 2) exponentHigh
  have scaledPower := Nat.mul_le_mul_right
    (embeddedValue (B source)) powerBound
  have embeddedLower :
      3 * B source + 1 ≤ embeddedValue (B source) := by
    rw [embeddedValue_formula]
    have lower := three_value_le_two_A (B source)
    omega
  have scaledLower := Nat.mul_le_mul_left 8 embeddedLower
  have embeddedUpper : embeddedValue source ≤ 3 * source + 2 := by
    rw [embeddedValue_formula]
    have upper := A_double_le source
    omega
  omega

/-- A higher-valuation B transfer from below `2 * minimum` necessarily drops
below the minimum source. -/
theorem highTransfer_source_strict
    {minimum source exponent : Nat} (minimumPositive : 0 < minimum)
    (sourceBound : source < 2 * minimum)
    (exponentHigh : 3 ≤ exponent)
    (tail : IsConstantTail
      (A (Q (embeddedValue source) 1
        (1 - sourceASelectingBit source)))
      (embeddedValue (B source)) exponent
      (sourceASelectingBit source)) :
    B source < minimum := by
  have bound := eight_B_le_of_high_nonselected exponentHigh tail
  omega

/-- Three successive B-sources satisfy the exact affine estimate used in
Section 27. -/
theorem sixtyFour_BBB_le (value : Nat) :
    64 * B (B (B value)) ≤ 27 * value + 37 := by
  have first := four_B_le value
  have second := four_B_le (B value)
  have third := four_B_le (B (B value))
  omega

/-- Every source surviving Section 26 lies below twice the globally minimal
source parameter. -/
theorem transferredSource_lt_twice
    {source : Nat} (row : ValuationTwoResidue256 source) :
    transferredSource source < 2 * source := by
  cases row with
  | r10 u => rw [transferredSource_10]; omega
  | r31 u => rw [transferredSource_31]; omega
  | r53 u => rw [transferredSource_53]; omega
  | r95 u => rw [transferredSource_95]; omega
  | r160 u => rw [transferredSource_160]; omega
  | r202 u => rw [transferredSource_202]; omega
  | r224 u => rw [transferredSource_224]; omega
  | r245 u => rw [transferredSource_245]; omega

/-- Starting from any Section 26 survivor, three more B-source transfers
fall strictly below the original source. -/
theorem threeFurtherTransfers_source_strict
    {source : Nat} (row : ValuationTwoResidue256 source) :
    B (B (B (transferredSource source))) < source := by
  have tripleBound := sixtyFour_BBB_le (transferredSource source)
  cases row with
  | r10 u => rw [transferredSource_10] at tripleBound ⊢; omega
  | r31 u => rw [transferredSource_31] at tripleBound ⊢; omega
  | r53 u => rw [transferredSource_53] at tripleBound ⊢; omega
  | r95 u => rw [transferredSource_95] at tripleBound ⊢; omega
  | r160 u => rw [transferredSource_160] at tripleBound ⊢; omega
  | r202 u => rw [transferredSource_202] at tripleBound ⊢; omega
  | r224 u => rw [transferredSource_224] at tripleBound ⊢; omega
  | r245 u => rw [transferredSource_245] at tripleBound ⊢; omega

/-- Hence three further surviving B-source transfers are impossible. -/
theorem no_three_further_surviving_transfers
    {source : Nat} (row : ValuationTwoResidue256 source) :
    ¬ source ≤ B (B (B (transferredSource source))) := by
  intro survives
  have strict := threeFurtherTransfers_source_strict row
  omega

end ThreeNPlusMinusOne
