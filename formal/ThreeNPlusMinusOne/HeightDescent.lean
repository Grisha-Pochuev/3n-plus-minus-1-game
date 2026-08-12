import ThreeNPlusMinusOne.PhaseMatch

set_option autoImplicit false

/-!
# Phase-match proof-height descent (Section 22)

The four surviving suffix-length-three rows are proved symbolically for an
arbitrary parameter.  Their common child is a grandchild through either
branch of the lower-source WIN state, so every concrete finite winning proof
tree loses at least two levels.
-/

namespace ThreeNPlusMinusOne

/-- The ordinary returned state itself has canonical coefficient source
below the minimum whenever it satisfies the Section 19 affine bound. -/
theorem phaseMatch_returnedState_source_strict
    {source returnedSource rho : Nat}
    (sourcePositive : 0 < source)
    (returnBound : 8 * returnedSource ≤ 9 * source + 3)
    (coordinates : StateHasSource returnedSource rho) :
    rho < source := by
  obtain ⟨sourceExponent, tailExponent, tailBit, coefficient,
    tail, sourceData⟩ := coordinates
  have coefficientBound := tail.coefficient_le_half
  have embeddedBound := sourceData.embedded_le_coefficient
  rw [embeddedValue_formula] at embeddedBound
  omega

private theorem R_initial_zero (t : Nat) : R (288 * t + 2) = 36 * t := by
  by_cases tZero : t = 0
  · subst t
    simp
  calc
    R (288 * t + 2) = R (144 * t + 1) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (72 * t) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = 36 * t := by
      rw [R_of_boundary (by omega) (by omega)]
      omega

private theorem R_initial_ten (t : Nat) :
    R (288 * t + 93) = 36 * t + 11 := by
  calc
    R (288 * t + 93) = R (144 * t + 46) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (72 * t + 23) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = 36 * t + 11 := by
      rw [R_of_boundary (by omega) (by omega)]
      omega

private theorem R_initial_twenty_one (t : Nat) :
    R (288 * t + 194) = 36 * t + 24 := by
  calc
    R (288 * t + 194) = R (144 * t + 97) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (72 * t + 48) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = 36 * t + 24 := by
      rw [R_of_boundary (by omega) (by omega)]
      omega

private theorem R_initial_thirty_one (t : Nat) :
    R (288 * t + 285) = 36 * t + 35 := by
  calc
    R (288 * t + 285) = R (144 * t + 142) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (72 * t + 71) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = 36 * t + 35 := by
      rw [R_of_boundary (by omega) (by omega)]
      omega

/-- Section 22's identity `B(q₀)=B(A(source))` in all four phase-match
rows. -/
theorem phaseMatch_initialSide_zero (t : Nat) :
    B (Q (embeddedValue (32 * t)) 1
      (sourceASelectingBit (32 * t))) = B (A (32 * t)) := by
  have phase : sourceASelectingBit (32 * t) = 1 := by
    unfold sourceASelectingBit
    omega
  rw [phase]
  rw [show 32 * t = 16 * (2 * t) by omega, returnRow_zero]
  unfold B
  rw [show A (Q (embeddedValue (16 * (2 * t))) 1 1) = 288 * t + 2 by
    simp [A, Q, embeddedValue_formula]
    omega]
  rw [R_initial_zero]
  omega

theorem phaseMatch_initialSide_ten (t : Nat) :
    B (Q (embeddedValue (32 * t + 10)) 1
      (sourceASelectingBit (32 * t + 10))) = B (A (32 * t + 10)) := by
  have phase : sourceASelectingBit (32 * t + 10) = 0 := by
    unfold sourceASelectingBit
    omega
  rw [phase]
  rw [show 32 * t + 10 = 16 * (2 * t) + 10 by omega, returnRow_ten]
  unfold B
  rw [show A (Q (embeddedValue (16 * (2 * t) + 10)) 1 0) =
      288 * t + 93 by
    simp [A, Q, embeddedValue_formula]
    omega]
  rw [R_initial_ten]
  omega

theorem phaseMatch_initialSide_twenty_one (t : Nat) :
    B (Q (embeddedValue (32 * t + 21)) 1
      (sourceASelectingBit (32 * t + 21))) = B (A (32 * t + 21)) := by
  have phase : sourceASelectingBit (32 * t + 21) = 1 := by
    unfold sourceASelectingBit
    omega
  rw [phase]
  rw [show 32 * t + 21 = 16 * (2 * t + 1) + 5 by omega,
    returnRow_five]
  unfold B
  rw [show A (Q (embeddedValue (16 * (2 * t + 1) + 5)) 1 1) =
      288 * t + 194 by
    simp [A, Q, embeddedValue_formula]
    omega]
  rw [R_initial_twenty_one]
  omega

theorem phaseMatch_initialSide_thirty_one (t : Nat) :
    B (Q (embeddedValue (32 * t + 31)) 1
      (sourceASelectingBit (32 * t + 31))) = B (A (32 * t + 31)) := by
  have phase : sourceASelectingBit (32 * t + 31) = 0 := by
    unfold sourceASelectingBit
    omega
  rw [phase]
  rw [show 32 * t + 31 = 16 * (2 * t + 1) + 15 by omega,
    returnRow_fifteen]
  unfold B
  rw [show A (Q (embeddedValue (16 * (2 * t + 1) + 15)) 1 0) =
      288 * t + 285 by
    simp [A, Q, embeddedValue_formula]
    omega]
  rw [R_initial_thirty_one]
  omega

/-- At a globally minimum DRAW source, the exact ordinary side state in a
phase-match row is WIN because its canonical source is strictly smaller. -/
theorem minimumSource_phaseMatch_returned_winning
    {source : Nat} (sourcePositive : 0 < source)
    (minimum : MinimumDrawSource source)
    (initialDraw :
      Draw (Q (embeddedValue source) 1 (sourceASelectingBit source)))
    (initialSide :
      B (Q (embeddedValue source) 1 (sourceASelectingBit source)) =
        B (A source))
    (returnBound : 8 * B (A source) ≤ 9 * source + 3) :
    Winning (B (A source)) := by
  have returnedNotLosing : ¬ Losing (B (A source)) := by
    rw [← initialSide]
    exact initialDraw.children_not_losing.2
  have returnedPositive : 0 < B (A source) := by
    by_cases returnedZero : B (A source) = 0
    · apply False.elim
      apply returnedNotLosing
      rw [returnedZero]
      exact Losing.terminal
    · omega
  obtain ⟨rho, returnedCoordinates⟩ :=
    stateHasSource_exists returnedPositive
  have rhoDrop := phaseMatch_returnedState_source_strict
    sourcePositive returnBound returnedCoordinates
  have returnedNotDraw := minimum.not_draw_of_smaller
    returnedCoordinates rhoDrop
  exact winning_of_not_draw_and_not_losing
    returnedNotDraw returnedNotLosing

/-- Assemble an exact phase-match arithmetic diamond with the minimum-source
outcome argument, retaining concrete proof-tree heights. -/
theorem minimumSource_phaseMatch_heightDescent
    {source common : Nat}
    (sourcePositive : 0 < source)
    (minimum : MinimumDrawSource source)
    (initialDraw :
      Draw (Q (embeddedValue source) 1 (sourceASelectingBit source)))
    (initialSide :
      B (Q (embeddedValue source) 1 (sourceASelectingBit source)) =
        B (A source))
    (returnBound : 8 * B (A source) ≤ 9 * source + 3)
    (transfer : ∀ height, WinningTree (B (A source)) height →
      ∃ lowerHeight,
        WinningTree common lowerHeight ∧ lowerHeight + 2 ≤ height) :
    ∃ height lowerHeight,
      WinningTree (B (A source)) height ∧
        WinningTree common lowerHeight ∧ lowerHeight + 2 ≤ height := by
  obtain ⟨height, tree⟩ := minimumSource_phaseMatch_returned_winning
    sourcePositive minimum initialDraw initialSide returnBound
  obtain ⟨lowerHeight, lowerTree, lower⟩ := transfer height tree
  exact ⟨height, lowerHeight, tree, lowerTree, lower⟩

theorem B_sixteen_mul (t : Nat) : B (16 * t) = 12 * t := by
  unfold B
  rw [show A (16 * t) = 24 * t by simp [A]; omega]
  by_cases tZero : t = 0
  · subst t
    simp
  · rw [R_of_boundary (by omega) (by omega)]
    omega

theorem B_sixteen_mul_add_fifteen (t : Nat) :
    B (16 * t + 15) = 12 * t + 11 := by
  unfold B
  rw [show A (16 * t + 15) = 24 * t + 23 by simp [A]; omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

/-- The two nonexceptional side relations needed after the long rows have
already been excluded. -/
theorem sideRelation_zero (t : Nat) :
    B (A (16 * t)) = A (B (16 * t)) := by
  rw [returnRow_zero, B_sixteen_mul]
  simp [A]
  omega

theorem sideRelation_fifteen (t : Nat) :
    B (A (16 * t + 15)) = A (B (16 * t + 15)) := by
  rw [returnRow_fifteen, B_sixteen_mul_add_fifteen]
  simp [A]
  omega

private theorem R_length_three_zero (t : Nat) :
    R (1296 * t + 2) = 162 * t := by
  by_cases tZero : t = 0
  · subst t
    simp
  calc
    R (1296 * t + 2) = R (648 * t + 1) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (324 * t) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = 162 * t := by
      rw [R_of_boundary (by omega) (by omega)]
      omega

private theorem R_length_three_forty_two (t : Nat) :
    R (1296 * t + 429) = 162 * t + 53 := by
  calc
    R (1296 * t + 429) = R (648 * t + 214) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (324 * t + 107) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = 162 * t + 53 := by
      rw [R_of_boundary (by omega) (by omega)]
      omega

private theorem R_length_three_eighty_five (t : Nat) :
    R (1296 * t + 866) = 162 * t + 108 := by
  calc
    R (1296 * t + 866) = R (648 * t + 433) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (324 * t + 216) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = 162 * t + 108 := by
      rw [R_of_boundary (by omega) (by omega)]
      omega

private theorem R_length_three_one_hundred_twenty_seven (t : Nat) :
    R (1296 * t + 1293) = 162 * t + 161 := by
  calc
    R (1296 * t + 1293) = R (648 * t + 646) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (324 * t + 323) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = 162 * t + 161 := by
      rw [R_of_boundary (by omega) (by omega)]
      omega

private theorem commonGrandchild_of_sideRelation
    {z common : Nat} (commonBA : common = B (A z))
    (side : B (A z) = A (B z)) :
    CommonGrandchild common z := by
  exact ⟨Or.inr commonBA, Or.inl (commonBA.trans side)⟩

theorem phaseMatch_heightDiamond_zero (t : Nat) :
    let source := 128 * t
    let z := B (A source)
    let common :=
      B (Q (embeddedValue z) 1 (sourceASelectingBit source))
    CommonGrandchild common z := by
  dsimp only
  have returned : B (A (128 * t)) = 144 * t := by
    rw [show 128 * t = 16 * (8 * t) by omega, returnRow_zero]
    omega
  have phase : sourceASelectingBit (128 * t) = 1 := by
    unfold sourceASelectingBit
    omega
  have commonValue :
      B (Q (embeddedValue (B (A (128 * t)))) 1
        (sourceASelectingBit (128 * t))) = 162 * t := by
    rw [returned, phase]
    unfold B
    rw [show A (Q (embeddedValue (144 * t)) 1 1) = 1296 * t + 2 by
      simp [A, Q, embeddedValue_formula]
      omega]
    exact R_length_three_zero t
  apply commonGrandchild_of_sideRelation
  · rw [commonValue, returned]
    rw [show 144 * t = 16 * (9 * t) by omega, returnRow_zero]
    omega
  · rw [returned]
    simpa [show 144 * t = 16 * (9 * t) by omega] using
      sideRelation_zero (9 * t)

theorem phaseMatch_heightDiamond_forty_two (t : Nat) :
    let source := 128 * t + 42
    let z := B (A source)
    let common :=
      B (Q (embeddedValue z) 1 (sourceASelectingBit source))
    CommonGrandchild common z := by
  dsimp only
  have returned : B (A (128 * t + 42)) = 144 * t + 47 := by
    rw [show 128 * t + 42 = 16 * (2 * (4 * t + 1)) + 10 by omega,
      returnRow_ten]
    omega
  have phase : sourceASelectingBit (128 * t + 42) = 0 := by
    unfold sourceASelectingBit
    omega
  have commonValue :
      B (Q (embeddedValue (B (A (128 * t + 42)))) 1
        (sourceASelectingBit (128 * t + 42))) = 162 * t + 53 := by
    rw [returned, phase]
    unfold B
    rw [show A (Q (embeddedValue (144 * t + 47)) 1 0) =
        1296 * t + 429 by
      simp [A, Q, embeddedValue_formula]
      omega]
    exact R_length_three_forty_two t
  apply commonGrandchild_of_sideRelation
  · rw [commonValue, returned]
    rw [show 144 * t + 47 = 16 * (9 * t + 2) + 15 by omega,
      returnRow_fifteen]
    omega
  · rw [returned]
    simpa [show 144 * t + 47 = 16 * (9 * t + 2) + 15 by omega] using
      sideRelation_fifteen (9 * t + 2)

theorem phaseMatch_heightDiamond_eighty_five (t : Nat) :
    let source := 128 * t + 85
    let z := B (A source)
    let common :=
      B (Q (embeddedValue z) 1 (sourceASelectingBit source))
    CommonGrandchild common z := by
  dsimp only
  have returned : B (A (128 * t + 85)) = 144 * t + 96 := by
    rw [show 128 * t + 85 = 16 * (2 * (4 * t + 2) + 1) + 5 by omega,
      returnRow_five]
    omega
  have phase : sourceASelectingBit (128 * t + 85) = 1 := by
    unfold sourceASelectingBit
    omega
  have commonValue :
      B (Q (embeddedValue (B (A (128 * t + 85)))) 1
        (sourceASelectingBit (128 * t + 85))) = 162 * t + 108 := by
    rw [returned, phase]
    unfold B
    rw [show A (Q (embeddedValue (144 * t + 96)) 1 1) =
        1296 * t + 866 by
      simp [A, Q, embeddedValue_formula]
      omega]
    exact R_length_three_eighty_five t
  apply commonGrandchild_of_sideRelation
  · rw [commonValue, returned]
    rw [show 144 * t + 96 = 16 * (9 * t + 6) by omega,
      returnRow_zero]
    omega
  · rw [returned]
    simpa [show 144 * t + 96 = 16 * (9 * t + 6) by omega] using
      sideRelation_zero (9 * t + 6)

theorem phaseMatch_heightDiamond_one_hundred_twenty_seven (t : Nat) :
    let source := 128 * t + 127
    let z := B (A source)
    let common :=
      B (Q (embeddedValue z) 1 (sourceASelectingBit source))
    CommonGrandchild common z := by
  dsimp only
  have returned : B (A (128 * t + 127)) = 144 * t + 143 := by
    rw [show 128 * t + 127 = 16 * (2 * (4 * t + 3) + 1) + 15 by omega,
      returnRow_fifteen]
    omega
  have phase : sourceASelectingBit (128 * t + 127) = 0 := by
    unfold sourceASelectingBit
    omega
  have commonValue :
      B (Q (embeddedValue (B (A (128 * t + 127)))) 1
        (sourceASelectingBit (128 * t + 127))) = 162 * t + 161 := by
    rw [returned, phase]
    unfold B
    rw [show A (Q (embeddedValue (144 * t + 143)) 1 0) =
        1296 * t + 1293 by
      simp [A, Q, embeddedValue_formula]
      omega]
    exact R_length_three_one_hundred_twenty_seven t
  apply commonGrandchild_of_sideRelation
  · rw [commonValue, returned]
    rw [show 144 * t + 143 = 16 * (9 * t + 8) + 15 by omega,
      returnRow_fifteen]
    omega
  · rw [returned]
    simpa [show 144 * t + 143 = 16 * (9 * t + 8) + 15 by omega] using
      sideRelation_fifteen (9 * t + 8)

theorem phaseMatch_heightDrop_zero
    {t height : Nat} (tPositive : 0 < t)
    (tree : WinningTree (B (A (128 * t))) height) :
    ∃ lowerHeight,
      WinningTree
        (B (Q (embeddedValue (B (A (128 * t)))) 1
          (sourceASelectingBit (128 * t)))) lowerHeight ∧
        lowerHeight + 2 ≤ height := by
  apply tree.commonGrandchild_lower
  · have returned : B (A (128 * t)) = 144 * t := by
      rw [show 128 * t = 16 * (8 * t) by omega, returnRow_zero]
      omega
    have phase : sourceASelectingBit (128 * t) = 1 := by
      unfold sourceASelectingBit
      omega
    rw [returned, phase]
    unfold B
    rw [show A (Q (embeddedValue (144 * t)) 1 1) = 1296 * t + 2 by
      simp [A, Q, embeddedValue_formula]
      omega]
    rw [R_length_three_zero]
    omega
  · exact phaseMatch_heightDiamond_zero t

theorem phaseMatch_heightDrop_forty_two
    {t height : Nat}
    (tree : WinningTree (B (A (128 * t + 42))) height) :
    ∃ lowerHeight,
      WinningTree
        (B (Q (embeddedValue (B (A (128 * t + 42)))) 1
          (sourceASelectingBit (128 * t + 42)))) lowerHeight ∧
        lowerHeight + 2 ≤ height := by
  apply tree.commonGrandchild_lower
  · have returned : B (A (128 * t + 42)) = 144 * t + 47 := by
      rw [show 128 * t + 42 = 16 * (2 * (4 * t + 1)) + 10 by omega,
        returnRow_ten]
      omega
    have phase : sourceASelectingBit (128 * t + 42) = 0 := by
      unfold sourceASelectingBit
      omega
    rw [returned, phase]
    unfold B
    rw [show A (Q (embeddedValue (144 * t + 47)) 1 0) =
        1296 * t + 429 by
      simp [A, Q, embeddedValue_formula]
      omega]
    rw [R_length_three_forty_two]
    omega
  · exact phaseMatch_heightDiamond_forty_two t

theorem phaseMatch_heightDrop_eighty_five
    {t height : Nat}
    (tree : WinningTree (B (A (128 * t + 85))) height) :
    ∃ lowerHeight,
      WinningTree
        (B (Q (embeddedValue (B (A (128 * t + 85)))) 1
          (sourceASelectingBit (128 * t + 85)))) lowerHeight ∧
        lowerHeight + 2 ≤ height := by
  apply tree.commonGrandchild_lower
  · have returned : B (A (128 * t + 85)) = 144 * t + 96 := by
      rw [show 128 * t + 85 = 16 * (2 * (4 * t + 2) + 1) + 5 by omega,
        returnRow_five]
      omega
    have phase : sourceASelectingBit (128 * t + 85) = 1 := by
      unfold sourceASelectingBit
      omega
    rw [returned, phase]
    unfold B
    rw [show A (Q (embeddedValue (144 * t + 96)) 1 1) =
        1296 * t + 866 by
      simp [A, Q, embeddedValue_formula]
      omega]
    rw [R_length_three_eighty_five]
    omega
  · exact phaseMatch_heightDiamond_eighty_five t

theorem phaseMatch_heightDrop_one_hundred_twenty_seven
    {t height : Nat}
    (tree : WinningTree (B (A (128 * t + 127))) height) :
    ∃ lowerHeight,
      WinningTree
        (B (Q (embeddedValue (B (A (128 * t + 127)))) 1
          (sourceASelectingBit (128 * t + 127)))) lowerHeight ∧
        lowerHeight + 2 ≤ height := by
  apply tree.commonGrandchild_lower
  · have returned : B (A (128 * t + 127)) = 144 * t + 143 := by
      rw [show 128 * t + 127 = 16 * (2 * (4 * t + 3) + 1) + 15 by omega,
        returnRow_fifteen]
      omega
    have phase : sourceASelectingBit (128 * t + 127) = 0 := by
      unfold sourceASelectingBit
      omega
    rw [returned, phase]
    unfold B
    rw [show A (Q (embeddedValue (144 * t + 143)) 1 0) =
        1296 * t + 1293 by
      simp [A, Q, embeddedValue_formula]
      omega]
    rw [R_length_three_one_hundred_twenty_seven]
    omega
  · exact phaseMatch_heightDiamond_one_hundred_twenty_seven t

theorem minimumSource_phaseMatch_heightDescent_zero
    {t : Nat} (tPositive : 0 < t)
    (minimum : MinimumDrawSource (128 * t))
    (initialDraw :
      Draw (Q (embeddedValue (128 * t)) 1
        (sourceASelectingBit (128 * t)))) :
    let common :=
      B (Q (embeddedValue (B (A (128 * t)))) 1
        (sourceASelectingBit (128 * t)))
    ∃ height lowerHeight,
      WinningTree (B (A (128 * t))) height ∧
        WinningTree common lowerHeight ∧ lowerHeight + 2 ≤ height := by
  dsimp only
  apply minimumSource_phaseMatch_heightDescent (by omega) minimum initialDraw
  · simpa only [show 128 * t = 32 * (4 * t) by omega] using
      phaseMatch_initialSide_zero (4 * t)
  · simpa only [show 128 * t = 32 * (4 * t) by omega] using
      phaseMatch_return_bound_zero (4 * t)
  · intro height tree
    exact phaseMatch_heightDrop_zero tPositive tree

theorem minimumSource_phaseMatch_heightDescent_forty_two
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 42))
    (initialDraw :
      Draw (Q (embeddedValue (128 * t + 42)) 1
        (sourceASelectingBit (128 * t + 42)))) :
    let common :=
      B (Q (embeddedValue (B (A (128 * t + 42)))) 1
        (sourceASelectingBit (128 * t + 42)))
    ∃ height lowerHeight,
      WinningTree (B (A (128 * t + 42))) height ∧
        WinningTree common lowerHeight ∧ lowerHeight + 2 ≤ height := by
  dsimp only
  apply minimumSource_phaseMatch_heightDescent (by omega) minimum initialDraw
  · simpa only [show 128 * t + 42 = 32 * (4 * t + 1) + 10 by omega] using
      phaseMatch_initialSide_ten (4 * t + 1)
  · simpa only [show 128 * t + 42 = 32 * (4 * t + 1) + 10 by omega] using
      phaseMatch_return_bound_ten (4 * t + 1)
  · intro height tree
    exact phaseMatch_heightDrop_forty_two tree

theorem minimumSource_phaseMatch_heightDescent_eighty_five
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 85))
    (initialDraw :
      Draw (Q (embeddedValue (128 * t + 85)) 1
        (sourceASelectingBit (128 * t + 85)))) :
    let common :=
      B (Q (embeddedValue (B (A (128 * t + 85)))) 1
        (sourceASelectingBit (128 * t + 85)))
    ∃ height lowerHeight,
      WinningTree (B (A (128 * t + 85))) height ∧
        WinningTree common lowerHeight ∧ lowerHeight + 2 ≤ height := by
  dsimp only
  apply minimumSource_phaseMatch_heightDescent (by omega) minimum initialDraw
  · simpa only [show 128 * t + 85 = 32 * (4 * t + 2) + 21 by omega] using
      phaseMatch_initialSide_twenty_one (4 * t + 2)
  · simpa only [show 128 * t + 85 = 32 * (4 * t + 2) + 21 by omega] using
      phaseMatch_return_bound_twenty_one (4 * t + 2)
  · intro height tree
    exact phaseMatch_heightDrop_eighty_five tree

theorem minimumSource_phaseMatch_heightDescent_one_hundred_twenty_seven
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 127))
    (initialDraw :
      Draw (Q (embeddedValue (128 * t + 127)) 1
        (sourceASelectingBit (128 * t + 127)))) :
    let common :=
      B (Q (embeddedValue (B (A (128 * t + 127)))) 1
        (sourceASelectingBit (128 * t + 127)))
    ∃ height lowerHeight,
      WinningTree (B (A (128 * t + 127))) height ∧
        WinningTree common lowerHeight ∧ lowerHeight + 2 ≤ height := by
  dsimp only
  apply minimumSource_phaseMatch_heightDescent (by omega) minimum initialDraw
  · simpa only [show 128 * t + 127 = 32 * (4 * t + 3) + 31 by omega] using
      phaseMatch_initialSide_thirty_one (4 * t + 3)
  · simpa only [show 128 * t + 127 = 32 * (4 * t + 3) + 31 by omega] using
      phaseMatch_return_bound_thirty_one (4 * t + 3)
  · intro height tree
    exact phaseMatch_heightDrop_one_hundred_twenty_seven tree

end ThreeNPlusMinusOne
