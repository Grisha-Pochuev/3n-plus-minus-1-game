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
    rw [tailProductEven] at relation
    unfold Q
    simp
    rw [← tailProductEquation, tailProductEven]
    rcases even_or_odd returned with ⟨returnedHalf, rfl⟩ |
      ⟨returnedHalf, rfl⟩
    · simp at relation
      omega
    · simp at relation
      omega
  · subst complementBit
    have relation :
        2 * embeddedValue returned = 6 * tailProduct + 2 := by
      simpa using signedRelation
    rw [tailProductEven] at relation
    unfold Q
    simp
    rw [← tailProductEquation, tailProductEven]
    rcases even_or_odd returned with ⟨returnedHalf, rfl⟩ |
      ⟨returnedHalf, rfl⟩
    · simp at relation
      omega
    · simp at relation
      omega

/-- A tail product at exponent at least two is automatically even. -/
theorem exponentThree_tailProduct_even
    {source exponent tailProduct : Nat}
    (exponentLarge : 2 ≤ exponent)
    (tailProductEquation :
      tailProduct = embeddedValue source * 2 ^ (exponent - 1)) :
    ∃ half, tailProduct = 2 * half := by
  refine ⟨embeddedValue source * 2 ^ (exponent - 2), ?_⟩
  rw [tailProductEquation]
  obtain ⟨rest, hrest⟩ : ∃ rest, exponent - 1 = rest + 1 :=
    ⟨exponent - 2, by omega⟩
  rw [hrest]
  simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

/-- The two concrete signed valuation equations produce the scaled relation
used by the conditional coordinate bridge. -/
theorem exponentThree_signed_relation_of_valuations
    {side returned source exponent tailBit tailProduct : Nat}
    (bit : Bit tailBit)
    (exponentLarge : 2 ≤ exponent)
    (tailProductEquation :
      tailProduct = embeddedValue source * 2 ^ (exponent - 1))
    (firstValuation :
      9 * embeddedValue side + 1 - 2 * tailBit =
        2 ^ exponent * embeddedValue source)
    (returnValuation :
      27 * embeddedValue side + 1 - 2 * tailBit =
        2 * embeddedValue returned) :
    2 * embeddedValue returned =
      if tailBit = 0 then 6 * tailProduct - 2
      else 6 * tailProduct + 2 := by
  have powerSplit : 2 ^ exponent = 2 * 2 ^ (exponent - 1) := by
    obtain ⟨rest, rfl⟩ : ∃ rest, exponent = rest + 1 :=
      ⟨exponent - 1, by omega⟩
    simp [Nat.pow_succ, Nat.mul_comm]
  have scaled :
      2 ^ exponent * embeddedValue source = 2 * tailProduct := by
    rw [powerSplit, tailProductEquation]
    simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
  rw [scaled] at firstValuation
  rcases bit with rfl | rfl
  · simp at firstValuation returnValuation ⊢
    omega
  · simp at firstValuation returnValuation ⊢
    omega

/-- Full arithmetic Section 33 coordinate lemma: the exact signed valuation
equations imply the canonical lower-exponent `Q` coordinate. -/
theorem exponentThree_return_Q_coordinate_from_valuations
    {side returned source exponent tailBit tailProduct : Nat}
    (bit : Bit tailBit)
    (exponentLarge : 2 ≤ exponent)
    (tailProductEquation :
      tailProduct = embeddedValue source * 2 ^ (exponent - 1))
    (firstValuation :
      9 * embeddedValue side + 1 - 2 * tailBit =
        2 ^ exponent * embeddedValue source)
    (returnValuation :
      27 * embeddedValue side + 1 - 2 * tailBit =
        2 * embeddedValue returned) :
    returned = Q (embeddedValue source) (exponent - 1) (1 - tailBit) := by
  obtain ⟨half, tailProductEven⟩ := exponentThree_tailProduct_even
    exponentLarge tailProductEquation
  have signedRelation := exponentThree_signed_relation_of_valuations bit
    exponentLarge tailProductEquation firstValuation returnValuation
  exact exponentThree_return_Q_coordinate_of_even_tail bit rfl
    tailProductEquation tailProductEven signedRelation

end ThreeNPlusMinusOne
