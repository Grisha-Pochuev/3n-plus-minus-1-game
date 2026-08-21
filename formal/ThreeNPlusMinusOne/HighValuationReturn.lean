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
    (_minimumDraw : MinimumDrawSource minimum)
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

/-- Once the signed numerator has been scaled to an even tail product, the
returned coordinate is exactly the lower-exponent constant tail.  The
remaining Section 33 obligation is to derive the two hypotheses
`tailProductEquation` and `tailProductEven` from the concrete valuation. -/
theorem exponentThree_return_Q_coordinate_of_even_tail
    {source returned exponent tailBit complementBit tailProduct half : Nat}
    (bit : Bit tailBit) (complement : complementBit = 1 - tailBit)
    (tailProductEquation :
      tailProduct = embeddedValue source * 2 ^ (exponent - 1))
    (tailProductEven : tailProduct = 2 * half)
    (signedRelation :
      2 * embeddedValue returned =
        if tailBit = 0 then 6 * tailProduct - 2
        else 6 * tailProduct + 2) :
    returned = Q (embeddedValue source) (exponent - 1) complementBit := by
  rcases bit with rfl | rfl
  · subst complementBit
    have relation :
        2 * embeddedValue returned = 6 * tailProduct - 2 := by
      simpa using signedRelation
    rw [tailProductEven] at relation ⊢
    have target :
        Q (embeddedValue source) (exponent - 1) 1 = 2 * half - 1 := by
      simp [Q, ← tailProductEquation, Nat.mul_comm]
    rw [target]
    rcases even_or_odd returned with ⟨returnedHalf, rfl⟩ |
      ⟨returnedHalf, rfl⟩
    · simp [embeddedValue_formula] at relation
      omega
    · simp [embeddedValue_formula] at relation
      omega
  · subst complementBit
    have relation :
        2 * embeddedValue returned = 6 * tailProduct + 2 := by
      simpa using signedRelation
    rw [tailProductEven] at relation ⊢
    have target :
        Q (embeddedValue source) (exponent - 1) 0 = 2 * half := by
      simp [Q, ← tailProductEquation, Nat.mul_comm]
    rw [target]
    rcases even_or_odd returned with ⟨returnedHalf, rfl⟩ |
      ⟨returnedHalf, rfl⟩
    · simp [embeddedValue_formula] at relation
      omega
    · simp [embeddedValue_formula] at relation
      omega

end ThreeNPlusMinusOne
