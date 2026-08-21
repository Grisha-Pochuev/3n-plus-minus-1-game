import ThreeNPlusMinusOne.LongSwitchBounds

set_option autoImplicit false

/-!
# High-valuation return (Section 33)

Section 32 bounds already imply the first part of the Section 33 return
argument: a valuation-four (or larger) signed return cannot have a source
which survives the minimum-DRAW boundary.  This file records that implication
as a kernel-checked lemma.  The later phase-identification and exact
`Q_{v-1}` coordinate calculation remain separate obligations; keeping them
separate prevents the conditional global refinement from being hidden inside
an arithmetic shortcut.
-/

namespace ThreeNPlusMinusOne

/-- A high first valuation in the exponent-three branch forces a strict source
drop.  This is the contradiction used at the opening of Section 33. -/
theorem exponentThree_high_valuation_source_drops
    {minimum source side returned exponent tailBit : Nat}
    (minimumPositive : 0 < minimum)
    (minimumDraw : MinimumDrawSource minimum)
    (sourceBound : source < 2 * minimum)
    (sideBound : 48 * side ≤ 27 * source + 3)
    (bit : Bit tailBit)
    (valuation :
      9 * embeddedValue side + 1 - 2 * tailBit =
        2 ^ exponent * embeddedValue returned)
    (highValuation : 4 ≤ exponent) :
    returned < minimum := by
  by_cases sourceDrops : returned < minimum
  · exact sourceDrops
  · have returnedSurvives : minimum ≤ returned := by omega
    have exponentBound := exponentThree_firstValuation_le_three
      minimumPositive sourceBound sideBound bit returnedSurvives valuation
    omega

/-- The same return conclusion expressed as the exact disjunction used by
the signed-transition case split. -/
theorem exponentThree_high_valuation_return_case
    {minimum source side returned exponent tailBit : Nat}
    (minimumPositive : 0 < minimum)
    (minimumDraw : MinimumDrawSource minimum)
    (sourceBound : source < 2 * minimum)
    (sideBound : 48 * side ≤ 27 * source + 3)
    (bit : Bit tailBit)
    (valuation :
      9 * embeddedValue side + 1 - 2 * tailBit =
        2 ^ exponent * embeddedValue returned)
    (highValuation : 4 ≤ exponent) :
    returned < minimum ∨ exponent ≤ 3 := by
  left
  exact exponentThree_high_valuation_source_drops minimumPositive
    minimumDraw sourceBound sideBound bit valuation highValuation

end ThreeNPlusMinusOne
