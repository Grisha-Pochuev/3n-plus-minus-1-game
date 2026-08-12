import ThreeNPlusMinusOne.HeightDescent

set_option autoImplicit false

/-!
# Returned suffix length two (Section 23)
-/

namespace ThreeNPlusMinusOne

/-- Deleting the raw exponent-one source lift in its selected phase returns
the ordinary `A` child of the source. -/
theorem R_sourceLift_selected (source : Nat) :
    R (Q (embeddedValue source) 1 (sourceASelectingBit source)) =
      A source := by
  have phaseData := sourceASelectingBit_is_bit source
  have aParity := A_parity source
  have embeddedPositive := embeddedValue_positive source
  rcases phaseData with phaseZero | phaseOne
  · have aOdd : A source % 2 = 1 := by
      unfold sourceASelectingBit at phaseZero
      omega
    rw [phaseZero]
    rw [show Q (embeddedValue source) 1 0 =
        2 * embeddedValue source by simp [Q]; omega]
    rw [R_of_alternates (by omega) (by
      rw [show (2 * embeddedValue source) / 2 = embeddedValue source by
        omega]
      have embeddedOdd := embeddedValue_odd source
      obtain ⟨half, shape⟩ := embeddedOdd
      omega)]
    rw [show (2 * embeddedValue source) / 2 = embeddedValue source by omega]
    rw [R_of_boundary (by
      rw [embeddedValue]
      omega) (by
      rw [embeddedValue]
      omega)]
    simp [embeddedValue]
    omega
  · have aEven : A source % 2 = 0 := by
      unfold sourceASelectingBit at phaseOne
      omega
    rw [phaseOne]
    rw [show Q (embeddedValue source) 1 1 = 4 * A source + 1 by
      simp [Q, embeddedValue]
      omega]
    by_cases aZero : A source = 0
    · rw [aZero]
      simp
    · rw [R_of_alternates (by omega) (by omega)]
      rw [show (4 * A source + 1) / 2 = 2 * A source by omega]
      rw [R_of_boundary (by omega) (by omega)]
      omega

/-- Deleting the same lift in the opposite phase continues through the
ordinary alternating suffix and returns `B(source)`. -/
theorem R_sourceLift_nonselected (source : Nat) :
    R (Q (embeddedValue source) 1
      (1 - sourceASelectingBit source)) = B source := by
  have phaseData := sourceASelectingBit_is_bit source
  have aParity := A_parity source
  have embeddedPositive := embeddedValue_positive source
  rcases phaseData with phaseZero | phaseOne
  · have aOdd : A source % 2 = 1 := by
      unfold sourceASelectingBit at phaseZero
      omega
    rw [phaseZero]
    rw [show Q (embeddedValue source) 1 (1 - 0) =
        4 * A source + 1 by
      simp [Q, embeddedValue]
      omega]
    rw [R_of_alternates (by omega) (by omega)]
    rw [show (4 * A source + 1) / 2 = 2 * A source by omega]
    rw [R_of_alternates (by omega) (by omega)]
    rw [show (2 * A source) / 2 = A source by omega]
    rfl
  · have aEven : A source % 2 = 0 := by
      unfold sourceASelectingBit at phaseOne
      omega
    rw [phaseOne]
    rw [show Q (embeddedValue source) 1 (1 - 1) =
        2 * embeddedValue source by simp [Q]; omega]
    rw [R_of_alternates (by omega) (by
      rw [show (2 * embeddedValue source) / 2 = embeddedValue source by
        omega]
      have embeddedOdd := embeddedValue_odd source
      obtain ⟨half, shape⟩ := embeddedOdd
      omega)]
    rw [show (2 * embeddedValue source) / 2 = embeddedValue source by omega]
    rw [show embeddedValue source = 2 * A source + 1 by rfl]
    by_cases aZero : A source = 0
    · rw [aZero]
      unfold B
      rw [aZero]
      simp
    · rw [R_of_alternates (by omega) (by omega)]
      rw [show (2 * A source + 1) / 2 = A source by omega]
      rfl

/-- Arithmetic content shared by all eight suffix-length-two rows. -/
def LengthTwoFrame (source : Nat) : Prop :=
  let phase := sourceASelectingBit source
  let returned := B (A source)
  let lower := Q (embeddedValue returned) 1 phase
  let common := A (A returned)
  B lower = common ∧
    A (A lower) = Q (embeddedValue common) 1 phase

private theorem lengthTwoFrame_of_shape
    {source phase : Nat} (phaseData : Bit phase)
    (phaseEquation : sourceASelectingBit source = phase)
    (commonParity : A (A (B (A source))) % 2 = phase)
    (lowerShape :
      A (Q (embeddedValue (B (A source))) 1 phase) =
        4 * A (A (B (A source))) + 1 + phase) :
    LengthTwoFrame source := by
  dsimp [LengthTwoFrame]
  rw [phaseEquation]
  let common := A (A (B (A source)))
  have commonParity' : common % 2 = phase := by
    simpa [common] using commonParity
  constructor
  · change R (A (Q (embeddedValue (B (A source))) 1 phase)) = common
    rw [lowerShape]
    change R (4 * common + 1 + phase) = common
    rcases phaseData with phaseZero | phaseOne
    · rw [phaseZero] at commonParity' ⊢
      simp only [Nat.add_zero]
      by_cases commonZero : common = 0
      · rw [commonZero]
        exact R_one
      · rw [R_of_alternates (by omega) (by omega)]
        rw [show (4 * common + 1) / 2 = 2 * common by omega]
        rw [R_of_boundary (by omega) (by omega)]
        omega
    · rw [phaseOne] at commonParity' ⊢
      rw [show 4 * common + 1 + 1 = 4 * common + 2 by omega]
      rw [R_of_alternates (by omega) (by omega)]
      rw [show (4 * common + 2) / 2 = 2 * common + 1 by omega]
      rw [R_of_boundary (by omega) (by omega)]
      omega
  · rw [lowerShape]
    change A (4 * common + 1 + phase) =
      Q (embeddedValue common) 1 phase
    rcases phaseData with phaseZero | phaseOne
    · rw [phaseZero] at commonParity' ⊢
      obtain ⟨half, commonShape⟩ : ∃ half, common = 2 * half :=
        ⟨common / 2, by omega⟩
      rw [commonShape]
      simp [A, Q, embeddedValue]
      omega
    · rw [phaseOne] at commonParity' ⊢
      obtain ⟨half, commonShape⟩ : ∃ half, common = 2 * half + 1 :=
        ⟨common / 2, by omega⟩
      rw [commonShape]
      simp [A, Q, embeddedValue]
      omega

theorem LengthTwoFrame.returned_eq_A
    {source : Nat} (frame : LengthTwoFrame source)
    (samePhase :
      sourceASelectingBit source =
        sourceASelectingBit (A (A (B (A source))))) :
    B (A (Q (embeddedValue (B (A source))) 1
      (sourceASelectingBit source))) = A (A (A (B (A source)))) := by
  dsimp [LengthTwoFrame] at frame
  change R (A (A (Q (embeddedValue (B (A source))) 1
    (sourceASelectingBit source)))) = A (A (A (B (A source))))
  rw [frame.2, samePhase]
  exact R_sourceLift_selected (A (A (B (A source))))

theorem LengthTwoFrame.returned_eq_B
    {source : Nat} (frame : LengthTwoFrame source)
    (oppositePhase :
      sourceASelectingBit source =
        1 - sourceASelectingBit (A (A (B (A source))))) :
    B (A (Q (embeddedValue (B (A source))) 1
      (sourceASelectingBit source))) = B (A (A (B (A source)))) := by
  dsimp [LengthTwoFrame] at frame
  change R (A (A (Q (embeddedValue (B (A source))) 1
    (sourceASelectingBit source)))) = B (A (A (B (A source))))
  rw [frame.2, oppositePhase]
  exact R_sourceLift_nonselected (A (A (B (A source))))

private theorem lengthTwoFrame_row
    {source phase returned : Nat} (phaseData : Bit phase)
    (phaseEquation : sourceASelectingBit source = phase)
    (returnedEquation : B (A source) = returned)
    (commonParity : A (A returned) % 2 = phase)
    (lowerShape :
      A (Q (embeddedValue returned) 1 phase) =
        4 * A (A returned) + 1 + phase) :
    LengthTwoFrame source := by
  apply lengthTwoFrame_of_shape phaseData phaseEquation
  · rw [returnedEquation]
    exact commonParity
  · rw [returnedEquation]
    exact lowerShape

theorem lengthTwoFrame_ten (t : Nat) :
    LengthTwoFrame (128 * t + 10) := by
  apply lengthTwoFrame_row (phase := 0) (returned := 144 * t + 11)
  · exact Or.inl rfl
  · unfold sourceASelectingBit
    omega
  · rw [show 128 * t + 10 = 16 * (8 * t) + 10 by omega,
      returnRow_ten]
    omega
  · simp [A]
    omega
  · simp [A, Q, embeddedValue_formula]
    omega

theorem lengthTwoFrame_thirty_one (t : Nat) :
    LengthTwoFrame (128 * t + 31) := by
  apply lengthTwoFrame_row (phase := 0) (returned := 144 * t + 35)
  · exact Or.inl rfl
  · unfold sourceASelectingBit
    omega
  · rw [show 128 * t + 31 = 16 * (8 * t + 1) + 15 by omega,
      returnRow_fifteen]
    omega
  · simp [A]
    omega
  · simp [A, Q, embeddedValue_formula]
    omega

theorem lengthTwoFrame_thirty_two (t : Nat) :
    LengthTwoFrame (128 * t + 32) := by
  apply lengthTwoFrame_row (phase := 1) (returned := 144 * t + 36)
  · exact Or.inr rfl
  · unfold sourceASelectingBit
    omega
  · rw [show 128 * t + 32 = 16 * (8 * t + 2) by omega,
      returnRow_zero]
    omega
  · simp [A]
    omega
  · simp [A, Q, embeddedValue_formula]
    omega

theorem lengthTwoFrame_fifty_three (t : Nat) :
    LengthTwoFrame (128 * t + 53) := by
  apply lengthTwoFrame_row (phase := 1) (returned := 144 * t + 60)
  · exact Or.inr rfl
  · unfold sourceASelectingBit
    omega
  · rw [show 128 * t + 53 = 16 * (8 * t + 3) + 5 by omega,
      returnRow_five]
    omega
  · simp [A]
    omega
  · simp [A, Q, embeddedValue_formula]
    omega

theorem lengthTwoFrame_seventy_four (t : Nat) :
    LengthTwoFrame (128 * t + 74) := by
  apply lengthTwoFrame_row (phase := 0) (returned := 144 * t + 83)
  · exact Or.inl rfl
  · unfold sourceASelectingBit
    omega
  · rw [show 128 * t + 74 = 16 * (8 * t + 4) + 10 by omega,
      returnRow_ten]
    omega
  · simp [A]
    omega
  · simp [A, Q, embeddedValue_formula]
    omega

theorem lengthTwoFrame_ninety_five (t : Nat) :
    LengthTwoFrame (128 * t + 95) := by
  apply lengthTwoFrame_row (phase := 0) (returned := 144 * t + 107)
  · exact Or.inl rfl
  · unfold sourceASelectingBit
    omega
  · rw [show 128 * t + 95 = 16 * (8 * t + 5) + 15 by omega,
      returnRow_fifteen]
    omega
  · simp [A]
    omega
  · simp [A, Q, embeddedValue_formula]
    omega

theorem lengthTwoFrame_ninety_six (t : Nat) :
    LengthTwoFrame (128 * t + 96) := by
  apply lengthTwoFrame_row (phase := 1) (returned := 144 * t + 108)
  · exact Or.inr rfl
  · unfold sourceASelectingBit
    omega
  · rw [show 128 * t + 96 = 16 * (8 * t + 6) by omega,
      returnRow_zero]
    omega
  · simp [A]
    omega
  · simp [A, Q, embeddedValue_formula]
    omega

theorem lengthTwoFrame_one_hundred_seventeen (t : Nat) :
    LengthTwoFrame (128 * t + 117) := by
  apply lengthTwoFrame_row (phase := 1) (returned := 144 * t + 132)
  · exact Or.inr rfl
  · unfold sourceASelectingBit
    omega
  · rw [show 128 * t + 117 = 16 * (8 * t + 7) + 5 by omega,
      returnRow_five]
    omega
  · simp [A]
    omega
  · simp [A, Q, embeddedValue_formula]
    omega

theorem lengthTwo_returned_ten (t : Nat) :
    B (A (Q (embeddedValue (B (A (128 * t + 10)))) 1
      (sourceASelectingBit (128 * t + 10)))) =
        A (A (A (B (A (128 * t + 10))))) := by
  apply (lengthTwoFrame_ten t).returned_eq_A
  have returned : B (A (128 * t + 10)) = 144 * t + 11 := by
    rw [show 128 * t + 10 = 16 * (8 * t) + 10 by omega,
      returnRow_ten]
    omega
  rw [returned]
  unfold sourceASelectingBit
  simp [A]
  omega

theorem lengthTwo_returned_thirty_one (t : Nat) :
    B (A (Q (embeddedValue (B (A (128 * t + 31)))) 1
      (sourceASelectingBit (128 * t + 31)))) =
        B (A (A (B (A (128 * t + 31))))) := by
  apply (lengthTwoFrame_thirty_one t).returned_eq_B
  have returned : B (A (128 * t + 31)) = 144 * t + 35 := by
    rw [show 128 * t + 31 = 16 * (8 * t + 1) + 15 by omega,
      returnRow_fifteen]
    omega
  rw [returned]
  unfold sourceASelectingBit
  simp [A]
  omega

theorem lengthTwo_returned_thirty_two (t : Nat) :
    B (A (Q (embeddedValue (B (A (128 * t + 32)))) 1
      (sourceASelectingBit (128 * t + 32)))) =
        A (A (A (B (A (128 * t + 32))))) := by
  apply (lengthTwoFrame_thirty_two t).returned_eq_A
  have returned : B (A (128 * t + 32)) = 144 * t + 36 := by
    rw [show 128 * t + 32 = 16 * (8 * t + 2) by omega,
      returnRow_zero]
    omega
  rw [returned]
  unfold sourceASelectingBit
  simp [A]
  omega

theorem lengthTwo_returned_fifty_three (t : Nat) :
    B (A (Q (embeddedValue (B (A (128 * t + 53)))) 1
      (sourceASelectingBit (128 * t + 53)))) =
        B (A (A (B (A (128 * t + 53))))) := by
  apply (lengthTwoFrame_fifty_three t).returned_eq_B
  have returned : B (A (128 * t + 53)) = 144 * t + 60 := by
    rw [show 128 * t + 53 = 16 * (8 * t + 3) + 5 by omega,
      returnRow_five]
    omega
  rw [returned]
  unfold sourceASelectingBit
  simp [A]
  omega

theorem lengthTwo_returned_seventy_four (t : Nat) :
    B (A (Q (embeddedValue (B (A (128 * t + 74)))) 1
      (sourceASelectingBit (128 * t + 74)))) =
        B (A (A (B (A (128 * t + 74))))) := by
  apply (lengthTwoFrame_seventy_four t).returned_eq_B
  have returned : B (A (128 * t + 74)) = 144 * t + 83 := by
    rw [show 128 * t + 74 = 16 * (8 * t + 4) + 10 by omega,
      returnRow_ten]
    omega
  rw [returned]
  unfold sourceASelectingBit
  simp [A]
  omega

theorem lengthTwo_returned_ninety_five (t : Nat) :
    B (A (Q (embeddedValue (B (A (128 * t + 95)))) 1
      (sourceASelectingBit (128 * t + 95)))) =
        A (A (A (B (A (128 * t + 95))))) := by
  apply (lengthTwoFrame_ninety_five t).returned_eq_A
  have returned : B (A (128 * t + 95)) = 144 * t + 107 := by
    rw [show 128 * t + 95 = 16 * (8 * t + 5) + 15 by omega,
      returnRow_fifteen]
    omega
  rw [returned]
  unfold sourceASelectingBit
  simp [A]
  omega

theorem lengthTwo_returned_ninety_six (t : Nat) :
    B (A (Q (embeddedValue (B (A (128 * t + 96)))) 1
      (sourceASelectingBit (128 * t + 96)))) =
        B (A (A (B (A (128 * t + 96))))) := by
  apply (lengthTwoFrame_ninety_six t).returned_eq_B
  have returned : B (A (128 * t + 96)) = 144 * t + 108 := by
    rw [show 128 * t + 96 = 16 * (8 * t + 6) by omega,
      returnRow_zero]
    omega
  rw [returned]
  unfold sourceASelectingBit
  simp [A]
  omega

theorem lengthTwo_returned_one_hundred_seventeen (t : Nat) :
    B (A (Q (embeddedValue (B (A (128 * t + 117)))) 1
      (sourceASelectingBit (128 * t + 117)))) =
        A (A (A (B (A (128 * t + 117))))) := by
  apply (lengthTwoFrame_one_hundred_seventeen t).returned_eq_A
  have returned : B (A (128 * t + 117)) = 144 * t + 132 := by
    rw [show 128 * t + 117 = 16 * (8 * t + 7) + 5 by omega,
      returnRow_five]
    omega
  rw [returned]
  unfold sourceASelectingBit
  simp [A]
  omega

theorem A_double_le (value : Nat) : 2 * A value ≤ 3 * value + 1 := by
  unfold A
  omega

/-- The canonical coefficient source of the returned ordinary child in any
length-two row is below the globally minimal source. -/
theorem lengthTwo_returnedChild_source_strict
    {source returned common child rho : Nat}
    (sourcePositive : 0 < source)
    (returnBound : 8 * returned ≤ 9 * source + 3)
    (commonEquation : common = A (A returned))
    (childBound : child ≤ A common)
    (coordinates : StateHasSource child rho) :
    rho < source := by
  obtain ⟨sourceExponent, tailExponent, tailBit, coefficient,
    tail, sourceData⟩ := coordinates
  have coefficientBound := tail.coefficient_le_half
  have embeddedBound := sourceData.embedded_le_coefficient
  have firstA := A_double_le returned
  have secondA := A_double_le (A returned)
  have thirdA := A_double_le common
  rw [embeddedValue_formula] at embeddedBound
  rw [commonEquation] at childBound thirdA
  omega

theorem B_le_A (value : Nat) : B value ≤ A value := by
  unfold B
  exact Nat.le_trans (R_le_half (A value)) (Nat.div_le_self _ _)

theorem lengthTwo_returnedChild_source_strict_of_orientation
    {source rho : Nat}
    (sourcePositive : 0 < source)
    (returnBound : 8 * B (A source) ≤ 9 * source + 3)
    (orientation :
      B (A (Q (embeddedValue (B (A source))) 1
        (sourceASelectingBit source))) = A (A (A (B (A source)))) ∨
      B (A (Q (embeddedValue (B (A source))) 1
        (sourceASelectingBit source))) = B (A (A (B (A source)))))
    (coordinates :
      StateHasSource
        (B (A (Q (embeddedValue (B (A source))) 1
          (sourceASelectingBit source)))) rho) :
    rho < source := by
  refine lengthTwo_returnedChild_source_strict
    (source := source) (returned := B (A source))
    (common := A (A (B (A source))))
    (child := B (A (Q (embeddedValue (B (A source))) 1
      (sourceASelectingBit source))))
    sourcePositive returnBound rfl ?_ coordinates
  rcases orientation with returnedA | returnedB
  · rw [returnedA]
    exact Nat.le_refl _
  · rw [returnedB]
    exact B_le_A (A (A (B (A source))))

/-- The common child in every phase-match adjacent frame is WIN at a global
minimum source, and at least one member of the adjacent pair is DRAW. -/
theorem minimumSource_phaseMatch_common_winning
    {source : Nat} (sourceLarge : 4 ≤ source)
    (minimum : MinimumDrawSource source)
    (initialDraw :
      Draw (Q (embeddedValue source) 1 (sourceASelectingBit source)))
    (frame : PhaseMatchAdjacentFrame source)
    (returnBound : 8 * B (A source) ≤ 9 * source + 3) :
    let phase := sourceASelectingBit source
    let returned := B (A source)
    let lower := Q (embeddedValue returned) 1 phase
    let upper := Q (embeddedValue returned) 2 phase
    Winning (B lower) ∧ (Draw lower ∨ Draw upper) := by
  dsimp only
  let phase := sourceASelectingBit source
  let returned := B (A source)
  let parent := Q (embeddedValue (A source)) 1 (1 - phase)
  let lower := Q (embeddedValue returned) 1 phase
  let upper := Q (embeddedValue returned) 2 phase
  dsimp [PhaseMatchAdjacentFrame] at frame
  have phaseMatch : sourceASelectingBit returned = phase := by
    simpa [returned, phase] using frame.1
  have parentB : B parent = lower := by
    simpa [parent, lower, returned, phase] using frame.2.1
  have parentA : A parent = upper := by
    simpa [parent, upper, returned, phase] using frame.2.2
  have firstStep := minimumSource_sourceLift_forces_next
    (by omega : 0 < source) minimum initialDraw
  have parentDraw : Draw parent := by
    simpa [parent, phase] using firstStep.2
  obtain ⟨next, move, nextDraw⟩ := parentDraw.has_draw_child
  have adjacentDraw : Draw lower ∨ Draw upper := by
    rcases move.2 with nextA | nextB
    · subst next
      rw [parentA] at nextDraw
      exact Or.inr nextDraw
    · subst next
      rw [parentB] at nextDraw
      exact Or.inl nextDraw
  have commonEquation : B upper = B lower := by
    exact (B_Q_one_eq_two (embeddedValue_positive returned)
      (embeddedValue_odd returned) (sourceASelectingBit_is_bit source)).symm
  have commonNotLosing : ¬ Losing (B lower) := by
    rcases adjacentDraw with lowerDraw | upperDraw
    · exact lowerDraw.children_not_losing.2
    · rw [← commonEquation]
      exact upperDraw.children_not_losing.2
  have commonPositive : 0 < B lower := by
    by_cases commonZero : B lower = 0
    · apply False.elim
      apply commonNotLosing
      rw [commonZero]
      exact Losing.terminal
    · omega
  obtain ⟨rho, commonCoordinates⟩ :=
    stateHasSource_exists commonPositive
  have canonicalCoordinates :
      StateHasSource
        (B (Q (embeddedValue returned) 1
          (sourceASelectingBit returned))) rho := by
    rw [phaseMatch]
    simpa [lower, phase] using commonCoordinates
  have rhoDrop := phaseMatch_commonChild_source_strict
    sourceLarge returnBound canonicalCoordinates
  have commonNotDraw := minimum.not_draw_of_smaller
    commonCoordinates rhoDrop
  exact ⟨winning_of_not_draw_and_not_losing
    commonNotDraw commonNotLosing, adjacentDraw⟩

def LengthTwoOutcomeFork (source : Nat) : Prop :=
  let phase := sourceASelectingBit source
  let returned := B (A source)
  let lower := Q (embeddedValue returned) 1 phase
  let upper := Q (embeddedValue returned) 2 phase
  let lowerExpanding := A lower
  let returnedChild := B lowerExpanding
  ((Draw lower ∧ Draw lowerExpanding ∧ Draw (A lowerExpanding) ∧
      Winning returnedChild) ∨
    (Winning lower ∧ Losing lowerExpanding ∧ Draw upper ∧
      Draw (A upper) ∧ Winning returnedChild))

def LengthTwoOtherChildLosing (source : Nat) : Prop :=
  let phase := sourceASelectingBit source
  let returned := B (A source)
  let lower := Q (embeddedValue returned) 1 phase
  let common := A (A returned)
  let returnedChild := B (A lower)
  (returnedChild = A common ∧ Losing (B common)) ∨
    (returnedChild = B common ∧ Losing (A common))

/-- Complete forced outcome fork of Section 23, parameterized only by the
already explicit arithmetic orientation of the returned ordinary child. -/
theorem minimumSource_lengthTwo_outcomeFork
    {source : Nat} (sourceLarge : 4 ≤ source)
    (minimum : MinimumDrawSource source)
    (initialDraw :
      Draw (Q (embeddedValue source) 1 (sourceASelectingBit source)))
    (phaseFrame : PhaseMatchAdjacentFrame source)
    (lengthFrame : LengthTwoFrame source)
    (returnBound : 8 * B (A source) ≤ 9 * source + 3)
    (orientation :
      B (A (Q (embeddedValue (B (A source))) 1
        (sourceASelectingBit source))) = A (A (A (B (A source)))) ∨
      B (A (Q (embeddedValue (B (A source))) 1
        (sourceASelectingBit source))) = B (A (A (B (A source))))) :
    LengthTwoOutcomeFork source ∧ LengthTwoOtherChildLosing source := by
  let phase := sourceASelectingBit source
  let returned := B (A source)
  let parent := Q (embeddedValue (A source)) 1 (1 - phase)
  let lower := Q (embeddedValue returned) 1 phase
  let upper := Q (embeddedValue returned) 2 phase
  let common := A (A returned)
  let lowerExpanding := A lower
  let returnedChild := B lowerExpanding
  have commonAndDraw := minimumSource_phaseMatch_common_winning
    sourceLarge minimum initialDraw phaseFrame returnBound
  have commonWinning : Winning (B lower) := by
    simpa [phase, returned, lower] using commonAndDraw.1
  have adjacentDraw : Draw lower ∨ Draw upper := by
    simpa [phase, returned, lower, upper] using commonAndDraw.2
  have lengthData := lengthFrame
  dsimp [LengthTwoFrame] at lengthData
  have commonEquation : B lower = common := by
    simpa [phase, returned, lower, common] using lengthData.1
  have commonWinning' : Winning common := by
    rw [← commonEquation]
    exact commonWinning
  have phaseData : Bit phase := by
    simpa [phase] using sourceASelectingBit_is_bit source
  have lowerPositive : 0 < lower := by
    dsimp [lower]
    simp [Q]
    have embeddedPositive := embeddedValue_positive returned
    rcases phaseData with phaseZero | phaseOne <;> omega
  have firstStep := minimumSource_sourceLift_forces_next
    (by omega : 0 < source) minimum initialDraw
  have parentDraw : Draw parent := by
    simpa [parent, phase] using firstStep.2
  have phaseDataRaw := phaseFrame
  dsimp [PhaseMatchAdjacentFrame] at phaseDataRaw
  have parentB : B parent = lower := by
    simpa [parent, lower, returned, phase] using phaseDataRaw.2.1
  have lowerNotLosing : ¬ Losing lower := by
    rw [← parentB]
    exact parentDraw.children_not_losing.2
  have returnedChildPositive : 0 < returnedChild := by
    have returnedNotLosing : ¬ Losing returnedChild := by
      by_cases lowerDraw : Draw lower
      · dsimp [returnedChild, lowerExpanding]
        have expandingDraw := lowerDraw.A_of_B_winning (by
          rw [commonEquation]
          exact commonWinning')
        exact expandingDraw.children_not_losing.2
      · have lowerWinning := winning_of_not_draw_and_not_losing
          lowerDraw lowerNotLosing
        have expandingLosing : Losing lowerExpanding := by
          dsimp [lowerExpanding]
          apply lowerWinning.A_losing_of_B_not_losing
          rw [commonEquation]
          exact commonWinning'.not_losing
        have children := expandingLosing.children_winning (A_pos lowerPositive)
        exact children.2.not_losing
    by_cases returnedZero : returnedChild = 0
    · apply False.elim
      apply returnedNotLosing
      rw [returnedZero]
      exact Losing.terminal
    · omega
  obtain ⟨rho, returnedCoordinates⟩ :=
    stateHasSource_exists returnedChildPositive
  have returnedCoordinates' :
      StateHasSource
        (B (A (Q (embeddedValue (B (A source))) 1
          (sourceASelectingBit source)))) rho := by
    simpa [returnedChild, lowerExpanding, lower, returned, phase] using
      returnedCoordinates
  have rhoDrop := lengthTwo_returnedChild_source_strict_of_orientation
    (by omega : 0 < source) returnBound orientation returnedCoordinates'
  have returnedNotDraw := minimum.not_draw_of_smaller
    returnedCoordinates rhoDrop
  have forkAndReturnedWinning :
      LengthTwoOutcomeFork source ∧ Winning returnedChild := by
    by_cases lowerDraw : Draw lower
    · have expandingDraw : Draw lowerExpanding := by
        dsimp [lowerExpanding]
        apply lowerDraw.A_of_B_winning
        rw [commonEquation]
        exact commonWinning'
      have returnedNotLosing : ¬ Losing returnedChild := by
        dsimp [returnedChild, lowerExpanding]
        exact expandingDraw.children_not_losing.2
      have returnedWinning := winning_of_not_draw_and_not_losing
        returnedNotDraw returnedNotLosing
      have liftedDraw : Draw (A lowerExpanding) := by
        apply expandingDraw.A_of_B_winning
        simpa [returnedChild] using returnedWinning
      refine ⟨?_, returnedWinning⟩
      left
      exact ⟨lowerDraw, expandingDraw, liftedDraw, returnedWinning⟩
    · have lowerWinning := winning_of_not_draw_and_not_losing
        lowerDraw lowerNotLosing
      have upperDraw : Draw upper := by
        exact adjacentDraw.resolve_left lowerDraw
      have expandingLosing : Losing lowerExpanding := by
        dsimp [lowerExpanding]
        apply lowerWinning.A_losing_of_B_not_losing
        rw [commonEquation]
        exact commonWinning'.not_losing
      have returnedWinning : Winning returnedChild := by
        dsimp [returnedChild, lowerExpanding]
        exact (expandingLosing.children_winning (A_pos lowerPositive)).2
      have upperCommon : B upper = common := by
        calc
          B upper = B lower := (B_Q_one_eq_two
            (embeddedValue_positive returned) (embeddedValue_odd returned)
            phaseData).symm
          _ = common := commonEquation
      have highDraw : Draw (A upper) := by
        apply upperDraw.A_of_B_winning
        rw [upperCommon]
        exact commonWinning'
      refine ⟨?_, returnedWinning⟩
      right
      exact ⟨lowerWinning, expandingLosing, upperDraw, highDraw,
        returnedWinning⟩
  have otherChild : LengthTwoOtherChildLosing source := by
    rcases orientation with returnedA | returnedB
    · left
      refine ⟨?_, ?_⟩
      · simpa [returnedChild, lowerExpanding, lower, returned, phase,
          common] using returnedA
      · apply commonWinning'.B_losing_of_A_not_losing
        rw [← returnedA]
        simpa [returnedChild, lowerExpanding, lower, returned, phase] using
          forkAndReturnedWinning.2.not_losing
    · right
      refine ⟨?_, ?_⟩
      · simpa [returnedChild, lowerExpanding, lower, returned, phase,
          common] using returnedB
      · apply commonWinning'.A_losing_of_B_not_losing
        rw [← returnedB]
        simpa [returnedChild, lowerExpanding, lower, returned, phase] using
          forkAndReturnedWinning.2.not_losing
  exact ⟨forkAndReturnedWinning.1, otherChild⟩

theorem minimumSource_lengthTwo_ten
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 10))
    (initialDraw : Draw (Q (embeddedValue (128 * t + 10)) 1
      (sourceASelectingBit (128 * t + 10)))) :
    LengthTwoOutcomeFork (128 * t + 10) ∧
      LengthTwoOtherChildLosing (128 * t + 10) := by
  apply minimumSource_lengthTwo_outcomeFork (by omega) minimum initialDraw
  · simpa only [show 128 * t + 10 = 32 * (4 * t) + 10 by omega] using
      phaseMatchAdjacentFrame_ten (4 * t)
  · exact lengthTwoFrame_ten t
  · simpa only [show 128 * t + 10 = 32 * (4 * t) + 10 by omega] using
      phaseMatch_return_bound_ten (4 * t)
  · exact Or.inl (lengthTwo_returned_ten t)

theorem minimumSource_lengthTwo_thirty_one
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 31))
    (initialDraw : Draw (Q (embeddedValue (128 * t + 31)) 1
      (sourceASelectingBit (128 * t + 31)))) :
    LengthTwoOutcomeFork (128 * t + 31) ∧
      LengthTwoOtherChildLosing (128 * t + 31) := by
  apply minimumSource_lengthTwo_outcomeFork (by omega) minimum initialDraw
  · simpa only [show 128 * t + 31 = 32 * (4 * t) + 31 by omega] using
      phaseMatchAdjacentFrame_thirty_one (4 * t)
  · exact lengthTwoFrame_thirty_one t
  · simpa only [show 128 * t + 31 = 32 * (4 * t) + 31 by omega] using
      phaseMatch_return_bound_thirty_one (4 * t)
  · exact Or.inr (lengthTwo_returned_thirty_one t)

theorem minimumSource_lengthTwo_thirty_two
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 32))
    (initialDraw : Draw (Q (embeddedValue (128 * t + 32)) 1
      (sourceASelectingBit (128 * t + 32)))) :
    LengthTwoOutcomeFork (128 * t + 32) ∧
      LengthTwoOtherChildLosing (128 * t + 32) := by
  apply minimumSource_lengthTwo_outcomeFork (by omega) minimum initialDraw
  · simpa only [show 128 * t + 32 = 32 * (4 * t + 1) by omega] using
      phaseMatchAdjacentFrame_zero (4 * t + 1)
  · exact lengthTwoFrame_thirty_two t
  · simpa only [show 128 * t + 32 = 32 * (4 * t + 1) by omega] using
      phaseMatch_return_bound_zero (4 * t + 1)
  · exact Or.inl (lengthTwo_returned_thirty_two t)

theorem minimumSource_lengthTwo_fifty_three
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 53))
    (initialDraw : Draw (Q (embeddedValue (128 * t + 53)) 1
      (sourceASelectingBit (128 * t + 53)))) :
    LengthTwoOutcomeFork (128 * t + 53) ∧
      LengthTwoOtherChildLosing (128 * t + 53) := by
  apply minimumSource_lengthTwo_outcomeFork (by omega) minimum initialDraw
  · simpa only [show 128 * t + 53 = 32 * (4 * t + 1) + 21 by omega] using
      phaseMatchAdjacentFrame_twenty_one (4 * t + 1)
  · exact lengthTwoFrame_fifty_three t
  · simpa only [show 128 * t + 53 = 32 * (4 * t + 1) + 21 by omega] using
      phaseMatch_return_bound_twenty_one (4 * t + 1)
  · exact Or.inr (lengthTwo_returned_fifty_three t)

theorem minimumSource_lengthTwo_seventy_four
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 74))
    (initialDraw : Draw (Q (embeddedValue (128 * t + 74)) 1
      (sourceASelectingBit (128 * t + 74)))) :
    LengthTwoOutcomeFork (128 * t + 74) ∧
      LengthTwoOtherChildLosing (128 * t + 74) := by
  apply minimumSource_lengthTwo_outcomeFork (by omega) minimum initialDraw
  · simpa only [show 128 * t + 74 = 32 * (4 * t + 2) + 10 by omega] using
      phaseMatchAdjacentFrame_ten (4 * t + 2)
  · exact lengthTwoFrame_seventy_four t
  · simpa only [show 128 * t + 74 = 32 * (4 * t + 2) + 10 by omega] using
      phaseMatch_return_bound_ten (4 * t + 2)
  · exact Or.inr (lengthTwo_returned_seventy_four t)

theorem minimumSource_lengthTwo_ninety_five
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 95))
    (initialDraw : Draw (Q (embeddedValue (128 * t + 95)) 1
      (sourceASelectingBit (128 * t + 95)))) :
    LengthTwoOutcomeFork (128 * t + 95) ∧
      LengthTwoOtherChildLosing (128 * t + 95) := by
  apply minimumSource_lengthTwo_outcomeFork (by omega) minimum initialDraw
  · simpa only [show 128 * t + 95 = 32 * (4 * t + 2) + 31 by omega] using
      phaseMatchAdjacentFrame_thirty_one (4 * t + 2)
  · exact lengthTwoFrame_ninety_five t
  · simpa only [show 128 * t + 95 = 32 * (4 * t + 2) + 31 by omega] using
      phaseMatch_return_bound_thirty_one (4 * t + 2)
  · exact Or.inl (lengthTwo_returned_ninety_five t)

theorem minimumSource_lengthTwo_ninety_six
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 96))
    (initialDraw : Draw (Q (embeddedValue (128 * t + 96)) 1
      (sourceASelectingBit (128 * t + 96)))) :
    LengthTwoOutcomeFork (128 * t + 96) ∧
      LengthTwoOtherChildLosing (128 * t + 96) := by
  apply minimumSource_lengthTwo_outcomeFork (by omega) minimum initialDraw
  · simpa only [show 128 * t + 96 = 32 * (4 * t + 3) by omega] using
      phaseMatchAdjacentFrame_zero (4 * t + 3)
  · exact lengthTwoFrame_ninety_six t
  · simpa only [show 128 * t + 96 = 32 * (4 * t + 3) by omega] using
      phaseMatch_return_bound_zero (4 * t + 3)
  · exact Or.inr (lengthTwo_returned_ninety_six t)

theorem minimumSource_lengthTwo_one_hundred_seventeen
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 117))
    (initialDraw : Draw (Q (embeddedValue (128 * t + 117)) 1
      (sourceASelectingBit (128 * t + 117)))) :
    LengthTwoOutcomeFork (128 * t + 117) ∧
      LengthTwoOtherChildLosing (128 * t + 117) := by
  apply minimumSource_lengthTwo_outcomeFork (by omega) minimum initialDraw
  · simpa only [show 128 * t + 117 = 32 * (4 * t + 3) + 21 by omega] using
      phaseMatchAdjacentFrame_twenty_one (4 * t + 3)
  · exact lengthTwoFrame_one_hundred_seventeen t
  · simpa only [show 128 * t + 117 = 32 * (4 * t + 3) + 21 by omega] using
      phaseMatch_return_bound_twenty_one (4 * t + 3)
  · exact Or.inl (lengthTwo_returned_one_hundred_seventeen t)

end ThreeNPlusMinusOne
