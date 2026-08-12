import ThreeNPlusMinusOne.MinimumSource

set_option autoImplicit false

/-!
# Exact source boundary transition (Section 17)
-/

namespace ThreeNPlusMinusOne

def sourceASelectingBit (source : Nat) : Nat :=
  1 - ((source / 2) % 2)

def sourceBoundaryValue (source tailBit : Nat) : Nat :=
  3 * embeddedValue source + 1 - 2 * tailBit

theorem sourceASelectingBit_is_bit (source : Nat) :
    Bit (sourceASelectingBit source) := by
  unfold sourceASelectingBit Bit
  omega

theorem A_parity (source : Nat) : A source % 2 = (source / 2) % 2 := by
  rcases even_or_odd source with ⟨half, rfl⟩ | ⟨half, rfl⟩
  · rw [A_even]
    omega
  · rw [A_odd]
    omega

theorem embeddedValue_mod_four_of_selectingBit_zero
    {source : Nat} (phase : sourceASelectingBit source = 0) :
    embeddedValue source % 4 = 3 := by
  rw [embeddedValue_formula]
  unfold sourceASelectingBit at phase
  omega

theorem embeddedValue_mod_four_of_selectingBit_one
    {source : Nat} (phase : sourceASelectingBit source = 1) :
    embeddedValue source % 4 = 1 := by
  rw [embeddedValue_formula]
  unfold sourceASelectingBit at phase
  omega

/-- The selected phase contains exactly one factor of two and selects `A`. -/
theorem sourceBoundary_selects_A (source : Nat) :
    sourceBoundaryValue source (sourceASelectingBit source) =
      2 * embeddedValue (A source) := by
  unfold sourceBoundaryValue sourceASelectingBit
  rw [embeddedValue_formula, embeddedValue_formula, A_parity]
  unfold A
  omega

theorem sourceBoundary_A_removeTwos (source : Nat) :
    RemoveTwos (sourceBoundaryValue source (sourceASelectingBit source))
      (embeddedValue (A source)) := by
  rw [sourceBoundary_selects_A]
  exact RemoveTwos.double (RemoveTwos.self (embeddedValue_odd (A source)))

/-- The `A`-selecting exponent-one lift lands on the embedded `A`-child. -/
theorem A_sourceLift_selected (source : Nat) :
    A (Q (embeddedValue source) 1 (sourceASelectingBit source)) =
      Q (embeddedValue (A source)) 1
        (1 - sourceASelectingBit source) := by
  rw [A_Q (embeddedValue_positive source)
    (sourceASelectingBit_is_bit source) (by omega : 1 ≤ 1)]
  have boundary := sourceBoundary_selects_A source
  have bit := sourceASelectingBit_is_bit source
  rcases bit with hzero | hone
  · rw [hzero] at boundary ⊢
    simp [Q, sourceBoundaryValue] at boundary ⊢
    omega
  · rw [hone] at boundary ⊢
    simp [Q, sourceBoundaryValue] at boundary ⊢
    omega

/-- The other phase is the alternating-core raw branch. -/
theorem sourceBoundary_other_eq_alternatingCore (source : Nat) :
    sourceBoundaryValue source (1 - sourceASelectingBit source) =
      2 * alternatingCore (A source) := by
  have hparity := A_parity source
  unfold sourceBoundaryValue sourceASelectingBit embeddedValue
  by_cases heven : A source % 2 = 0
  · simp [alternatingCore, heven]
    omega
  · simp [alternatingCore, heven]
    omega

/-- The nonselected phase has at least two factors of two. -/
theorem sourceBoundary_other_divisible_by_four (source : Nat) :
    ∃ quotient,
      sourceBoundaryValue source (1 - sourceASelectingBit source) =
        4 * quotient := by
  rw [sourceBoundary_other_eq_alternatingCore]
  by_cases heven : A source % 2 = 0
  · have hm : ∃ half, A source = 2 * half :=
      ⟨A source / 2, by omega⟩
    obtain ⟨half, hhalf⟩ := hm
    refine ⟨3 * half + 1, ?_⟩
    rw [hhalf]
    simp [alternatingCore]
    omega
  · have hodd : A source % 2 = 1 := by omega
    obtain ⟨half, hhalf⟩ : ∃ half, A source = 2 * half + 1 :=
      ⟨A source / 2, by omega⟩
    refine ⟨3 * half + 2, ?_⟩
    rw [hhalf]
    simp [alternatingCore]
    omega

/-- The other phase selects exactly `B(source)` after odd-part reduction. -/
theorem sourceBoundary_B_removeTwos (source : Nat) :
    RemoveTwos
      (sourceBoundaryValue source (1 - sourceASelectingBit source))
      (embeddedValue (B source)) := by
  rw [sourceBoundary_other_eq_alternatingCore]
  have core := RemoveTwos.double (alternatingCore_removeTwos (A source))
  simpa [B, embeddedValue] using core

/-- The nonselected lift has source `B(source)` and valuation at least two. -/
theorem sourceLift_nonselected_constantTail (source : Nat) :
    ∃ exponent,
      2 ≤ exponent ∧
        IsConstantTail
          (A (Q (embeddedValue source) 1
            (1 - sourceASelectingBit source)))
          (embeddedValue (B source)) exponent
          (sourceASelectingBit source) := by
  let raw := sourceBoundaryValue source
    (1 - sourceASelectingBit source)
  have remove : RemoveTwos raw (embeddedValue (B source)) := by
    simpa [raw] using sourceBoundary_B_removeTwos source
  obtain ⟨coefficientOdd, exponent, rawEquation⟩ := remove
  have divisible := sourceBoundary_other_divisible_by_four source
  obtain ⟨quotient, divisibleEquation⟩ := divisible
  have exponentAtLeastTwo : 2 ≤ exponent := by
    by_cases large : 2 ≤ exponent
    · exact large
    · have rawDivisible : raw = 4 * quotient := by
        simpa [raw] using divisibleEquation
      obtain ⟨half, coefficientEquation⟩ := coefficientOdd
      have small : exponent = 0 ∨ exponent = 1 := by omega
      rcases small with exponentZero | exponentOne
      · subst exponent
        simp only [Nat.pow_zero, Nat.one_mul] at rawEquation
        omega
      · subst exponent
        simp only [Nat.pow_one] at rawEquation
        omega
  have stateEquation :
      A (Q (embeddedValue source) 1
          (1 - sourceASelectingBit source)) =
        Q (embeddedValue (B source)) exponent
          (sourceASelectingBit source) := by
    have complementBit : Bit (1 - sourceASelectingBit source) := by
      have bit := sourceASelectingBit_is_bit source
      rcases bit with hzero | hone
      · right
        omega
      · left
        omega
    have expand := A_Q
      (coefficient := embeddedValue source) (exponent := 1)
      (tailBit := 1 - sourceASelectingBit source)
      (embeddedValue_positive source) complementBit
      (by omega : 1 ≤ 1)
    have rawEquation' :
        sourceBoundaryValue source (1 - sourceASelectingBit source) =
          2 ^ exponent * embeddedValue (B source) := by
      simpa [raw] using rawEquation
    have selectingBit := sourceASelectingBit_is_bit source
    rcases selectingBit with hzero | hone
    · rw [hzero] at expand rawEquation' ⊢
      rw [expand]
      simp [Q, sourceBoundaryValue, Nat.mul_comm] at expand rawEquation' ⊢
      omega
    · rw [hone] at expand rawEquation' ⊢
      rw [expand]
      simp [Q, sourceBoundaryValue, Nat.mul_comm] at expand rawEquation' ⊢
      omega
  exact ⟨exponent, exponentAtLeastTwo,
    ⟨embeddedValue_positive (B source), coefficientOdd,
      by omega, sourceASelectingBit_is_bit source, stateEquation⟩⟩

/-- The nonselected exponent-one lift has canonical source `B(source)`. -/
theorem sourceLift_nonselected_hasSource (source : Nat) :
    StateHasSource
      (A (Q (embeddedValue source) 1
        (1 - sourceASelectingBit source)))
      (B source) := by
  obtain ⟨exponent, _large, tail⟩ :=
    sourceLift_nonselected_constantTail source
  exact ⟨0, exponent, sourceASelectingBit source,
    embeddedValue (B source), tail, ⟨by simp⟩⟩

/-- The side child of a nonselected lift retains the same lower source. -/
theorem sourceLift_nonselected_side_hasSource (source : Nat) :
    StateHasSource
      (B (Q (embeddedValue source) 1
        (1 - sourceASelectingBit source)))
      (B source) := by
  obtain ⟨exponent, exponentLarge, tail⟩ :=
    sourceLift_nonselected_constantTail source
  have sideEquation :
      B (Q (embeddedValue source) 1
          (1 - sourceASelectingBit source)) =
        Q (embeddedValue (B source)) (exponent - 1)
          (sourceASelectingBit source) := by
    unfold B
    rw [tail.equation]
    exact R_Q tail.positive tail.bit exponentLarge
  have sideTail :
      IsConstantTail
        (B (Q (embeddedValue source) 1
          (1 - sourceASelectingBit source)))
        (embeddedValue (B source)) (exponent - 1)
        (sourceASelectingBit source) :=
    ⟨tail.positive, tail.odd, by omega, tail.bit, sideEquation⟩
  exact ⟨0, exponent - 1, sourceASelectingBit source,
    embeddedValue (B source), sideTail, ⟨by simp⟩⟩

/-- A minimum positive DRAW source cannot use the `B`-selecting phase. -/
theorem minimumSource_exponentOne_phase
    {source tailBit : Nat} (sourcePositive : 0 < source)
    (bit : Bit tailBit) (minimum : MinimumDrawSource source)
    (parentDraw : Draw (Q (embeddedValue source) 1 tailBit)) :
    tailBit = sourceASelectingBit source := by
  by_cases same : tailBit = sourceASelectingBit source
  · exact same
  · have selectingBit := sourceASelectingBit_is_bit source
    have other : tailBit = 1 - sourceASelectingBit source := by
      rcases bit with htailZero | htailOne <;>
        rcases selectingBit with hselectZero | hselectOne <;>
        omega
    have forced := minimumSource_boundary_forces_A_auto
      sourcePositive bit (Or.inl rfl) minimum parentDraw
    have childSource := sourceLift_nonselected_hasSource source
    rw [other] at forced
    have childNotDraw := minimum.not_draw_of_smaller childSource
      (B_strictly_contracts sourcePositive)
    exact False.elim (childNotDraw forced.2)

/--
At a globally minimum positive DRAW source, the selected exponent-one lift
has a winning common side child and its exact embedded `A`-child is DRAW.
-/
theorem minimumSource_sourceLift_forces_next
    {source : Nat} (sourcePositive : 0 < source)
    (minimum : MinimumDrawSource source)
    (parentDraw :
      Draw (Q (embeddedValue source) 1 (sourceASelectingBit source))) :
    Winning
        (B (Q (embeddedValue source) 1 (sourceASelectingBit source))) ∧
      Draw
        (Q (embeddedValue (A source)) 1
          (1 - sourceASelectingBit source)) := by
  have forced := minimumSource_boundary_forces_A_auto
    sourcePositive (sourceASelectingBit_is_bit source) (Or.inl rfl)
    minimum parentDraw
  constructor
  · exact forced.1
  · rw [← A_sourceLift_selected source]
    exact forced.2

/-- Full exponent-one Section 17 consequence, including forced phase. -/
theorem minimumSource_exponentOne_forces_next
    {source tailBit : Nat} (sourcePositive : 0 < source)
    (bit : Bit tailBit) (minimum : MinimumDrawSource source)
    (parentDraw : Draw (Q (embeddedValue source) 1 tailBit)) :
    tailBit = sourceASelectingBit source ∧
      Winning (B (Q (embeddedValue source) 1 tailBit)) ∧
      Draw
        (Q (embeddedValue (A source)) 1
          (1 - sourceASelectingBit source)) := by
  have phase := minimumSource_exponentOne_phase
    sourcePositive bit minimum parentDraw
  subst tailBit
  exact ⟨rfl, minimumSource_sourceLift_forces_next
    sourcePositive minimum parentDraw⟩

/--
Two selected lifts reproduce the ordinary side return.  If that returned
source is below the global minimum, the side is WIN and the other child is
forced to remain DRAW.
-/
theorem minimumSource_twoLift_sourceDrop
    {source : Nat} (sourcePositive : 0 < source)
    (minimum : MinimumDrawSource source)
    (parentDraw :
      Draw (Q (embeddedValue source) 1 (sourceASelectingBit source)))
    (secondPhaseNonselected :
      1 - sourceASelectingBit source =
        1 - sourceASelectingBit (A source))
    (returnedSourceDrops : B (A source) < source) :
    let second :=
      Q (embeddedValue (A source)) 1
        (1 - sourceASelectingBit source)
    Winning (B second) ∧ Draw (A second) := by
  dsimp only
  have firstStep := minimumSource_sourceLift_forces_next
    sourcePositive minimum parentDraw
  let second := Q (embeddedValue (A source)) 1
    (1 - sourceASelectingBit source)
  have secondDraw : Draw second := by
    simpa [second] using firstStep.2
  have sideSource : StateHasSource (B second) (B (A source)) := by
    have canonical := sourceLift_nonselected_side_hasSource (A source)
    simpa [second, secondPhaseNonselected] using canonical
  have sideNotDraw := minimum.not_draw_of_smaller
    sideSource returnedSourceDrops
  have sideNotLosing : ¬ Losing (B second) :=
    secondDraw.children_not_losing.2
  have sideWinning := winning_of_not_draw_and_not_losing
    sideNotDraw sideNotLosing
  exact ⟨sideWinning, secondDraw.A_of_B_winning sideWinning⟩

/-- At exponent two, the exact forced DRAW child is the factor-three lift. -/
theorem minimumSource_exponentTwo_forces_factor
    {source tailBit : Nat} (sourcePositive : 0 < source)
    (bit : Bit tailBit) (minimum : MinimumDrawSource source)
    (parentDraw : Draw (Q (embeddedValue source) 2 tailBit)) :
    Winning (B (Q (embeddedValue source) 2 tailBit)) ∧
      Draw (Q (3 * embeddedValue source) 1 tailBit) := by
  have forced := minimumSource_boundary_forces_A_auto
    sourcePositive bit (Or.inr rfl) minimum parentDraw
  refine ⟨forced.1, ?_⟩
  rw [← A_Q (embeddedValue_positive source) bit (by omega : 1 ≤ 2)]
  simpa using forced.2

end ThreeNPlusMinusOne
