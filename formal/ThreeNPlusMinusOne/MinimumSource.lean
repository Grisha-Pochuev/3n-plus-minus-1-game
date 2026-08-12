import ThreeNPlusMinusOne.Source
import ThreeNPlusMinusOne.Outcome

set_option autoImplicit false

/-!
# Minimum DRAW source

This file makes the minimum-source choice in Sections 17 and 137 explicit.
-/

namespace ThreeNPlusMinusOne

def StateHasSource (state source : Nat) : Prop :=
  ∃ sourceExponent tailExponent tailBit,
    IsSourceCoordinates state source sourceExponent tailExponent tailBit

theorem stateHasSource_exists {state : Nat} (positive : 0 < state) :
    ∃ source, StateHasSource state source := by
  obtain ⟨source, sourceExponent, tailExponent, tailBit, coordinates⟩ :=
    sourceCoordinates_exists positive
  exact ⟨source, sourceExponent, tailExponent, tailBit, coordinates⟩

theorem StateHasSource.unique {state first second : Nat}
    (firstSource : StateHasSource state first)
    (secondSource : StateHasSource state second) : first = second := by
  obtain ⟨firstSourceExponent, firstTailExponent, firstBit, firstData⟩ :=
    firstSource
  obtain ⟨secondSourceExponent, secondTailExponent, secondBit, secondData⟩ :=
    secondSource
  exact (firstData.unique secondData).1

private theorem exists_nat_minimal
    {property : Nat → Prop} (existsProperty : ∃ value, property value) :
    ∃ minimum, property minimum ∧
      ∀ value, property value → minimum ≤ value := by
  classical
  obtain ⟨witness, witnessProperty⟩ := existsProperty
  refine Nat.strongRecOn
    (motive := fun witness => property witness →
      ∃ minimum, property minimum ∧
        ∀ value, property value → minimum ≤ value)
    witness ?_ witnessProperty
  intro witness ih witnessProperty
  by_cases smaller : ∃ value, value < witness ∧ property value
  · obtain ⟨value, less, valueProperty⟩ := smaller
    exact ih value less valueProperty
  · exact ⟨witness, witnessProperty, by
      intro value valueProperty
      by_cases hless : value < witness
      · exact False.elim (smaller ⟨value, hless, valueProperty⟩)
      · omega⟩

def DrawAtSource (source : Nat) : Prop :=
  ∃ state, Draw state ∧ StateHasSource state source

structure MinimumDrawSource (source : Nat) : Prop where
  existsDraw : DrawAtSource source
  minimum : ∀ candidate, DrawAtSource candidate → source ≤ candidate

/-- Any nonempty DRAW set has a globally minimum canonical source. -/
theorem minimumDrawSource_exists (existsDraw : ∃ state, Draw state) :
    ∃ source, MinimumDrawSource source := by
  have existsSource : ∃ source, DrawAtSource source := by
    obtain ⟨state, stateDraw⟩ := existsDraw
    obtain ⟨source, stateSource⟩ := stateHasSource_exists stateDraw.positive
    exact ⟨source, state, stateDraw, stateSource⟩
  obtain ⟨source, atSource, minimum⟩ := exists_nat_minimal existsSource
  exact ⟨source, ⟨atSource, minimum⟩⟩

theorem MinimumDrawSource.not_draw_of_smaller
    {source state candidate : Nat} (minimum : MinimumDrawSource source)
    (stateSource : StateHasSource state candidate) (smaller : candidate < source) :
    ¬ Draw state := by
  intro stateDraw
  have := minimum.minimum candidate ⟨state, stateDraw, stateSource⟩
  omega

/-- Section 17's minimum-source boundary step at coefficient `J(source)`. -/
theorem minimumSource_boundary_forces_A
    {source exponent tailBit child childCoefficient childExponent childBit
      childSource childSourceExponent : Nat}
    (sourcePositive : 0 < source) (bit : Bit tailBit)
    (boundaryExponent : exponent = 1 ∨ exponent = 2)
    (minimum : MinimumDrawSource source)
    (parentDraw : Draw (Q (embeddedValue source) exponent tailBit))
    (childEquation : child = boundaryChild (embeddedValue source) tailBit)
    (childTail : IsConstantTail child childCoefficient childExponent childBit)
    (childSourceData :
      IsCoefficientSource childCoefficient childSource childSourceExponent) :
    Winning child ∧ Draw (A (Q (embeddedValue source) exponent tailBit)) := by
  have parentOdd : OddNat (embeddedValue source) := embeddedValue_odd source
  have parentLarge : 3 ≤ embeddedValue source := by
    rw [embeddedValue_formula]
    omega
  have childCoefficientStrict : childCoefficient < embeddedValue source :=
    boundaryChild_coefficient_strict parentLarge parentOdd bit
      childEquation childTail
  have childSourceStrict : childSource < source :=
    source_strict_of_coefficient_lt childSourceData childCoefficientStrict
  have childHasSource : StateHasSource child childSource := by
    exact ⟨childSourceExponent, childExponent, childBit,
      childCoefficient, childTail, childSourceData⟩
  have childNotDraw := minimum.not_draw_of_smaller
    childHasSource childSourceStrict
  have parentCoefficientPositive : 0 < embeddedValue source :=
    embeddedValue_positive source
  have hB : B (Q (embeddedValue source) exponent tailBit) = child := by
    rcases boundaryExponent with rfl | rfl
    · exact (B_Q_one_eq_boundaryChild parentCoefficientPositive bit).trans
        childEquation.symm
    · exact (B_Q_two_eq_boundaryChild parentCoefficientPositive parentOdd bit).trans
        childEquation.symm
  have childNotLosing : ¬ Losing child := by
    rw [← hB]
    exact parentDraw.children_not_losing.2
  have childWinning := winning_of_not_draw_and_not_losing
    childNotDraw childNotLosing
  exact ⟨childWinning, by
    apply parentDraw.A_of_B_winning
    rw [hB]
    exact childWinning⟩

/--
Coordinate-free form of the minimum-source boundary theorem.  The canonical
coordinates of the common child are derived internally, so callers cannot
choose an artificial coefficient or source for it.
-/
theorem minimumSource_boundary_forces_A_auto
    {source exponent tailBit : Nat}
    (sourcePositive : 0 < source) (bit : Bit tailBit)
    (boundaryExponent : exponent = 1 ∨ exponent = 2)
    (minimum : MinimumDrawSource source)
    (parentDraw : Draw (Q (embeddedValue source) exponent tailBit)) :
    Winning (B (Q (embeddedValue source) exponent tailBit)) ∧
      Draw (A (Q (embeddedValue source) exponent tailBit)) := by
  let parent := Q (embeddedValue source) exponent tailBit
  let child := B parent
  have childNotLosing : ¬ Losing child := by
    simpa [child, parent] using parentDraw.children_not_losing.2
  have childPositive : 0 < child := by
    have childNonzero : child ≠ 0 := by
      intro childZero
      apply childNotLosing
      rw [childZero]
      exact Losing.terminal
    omega
  obtain ⟨childCoefficient, childExponent, childBit, childTail⟩ :=
    constantTailCoordinates_exists childPositive
  obtain ⟨childSource, childSourceExponent, childSourceData⟩ :=
    coefficientSource_exists_unique childTail.positive childTail.odd
  have childEquation : child = boundaryChild (embeddedValue source) tailBit := by
    unfold child parent
    rcases boundaryExponent with exponentOne | exponentTwo
    · subst exponent
      exact B_Q_one_eq_boundaryChild (embeddedValue_positive source) bit
    · subst exponent
      exact B_Q_two_eq_boundaryChild (embeddedValue_positive source)
        (embeddedValue_odd source) bit
  have forced := minimumSource_boundary_forces_A
    (source := source) (exponent := exponent) (tailBit := tailBit)
    (child := child) (childCoefficient := childCoefficient)
    (childExponent := childExponent) (childBit := childBit)
    (childSource := childSource)
    (childSourceExponent := childSourceExponent)
    sourcePositive bit boundaryExponent minimum parentDraw childEquation
    childTail childSourceData
  simpa [child, parent] using forced

end ThreeNPlusMinusOne
