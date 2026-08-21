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

/-- The two signed numerator equations identify the returned source with the
canonical lower-exponent tail.  This is the exact arithmetic coordinate
calculation used after the Section 33 source-drop split. -/
theorem exponentThree_return_Q_coordinate
    {side returned source exponent tailBit complementBit : Nat}
    (bit : Bit tailBit) (complement : complementBit = 1 - tailBit)
    (exponentLarge : 4 ≤ exponent)
    (firstValuation :
      9 * embeddedValue side + 1 - 2 * tailBit =
        2 ^ exponent * embeddedValue source)
    (returnValuation :
      27 * embeddedValue side + 1 - 2 * tailBit =
        2 * embeddedValue returned) :
    returned = Q (embeddedValue source) (exponent - 1) complementBit := by
  rcases bit with rfl | rfl
  · subst complementBit
    have powerSplit : 2 ^ exponent = 2 * 2 ^ (exponent - 1) := by
      obtain ⟨rest, rfl⟩ : ∃ rest, exponent = rest + 1 :=
        ⟨exponent - 1, by omega⟩
      simp [Nat.pow_succ, Nat.mul_comm]
    have lowerPowerSplit : 2 ^ (exponent - 1) =
        2 * 2 ^ (exponent - 2) := by
      obtain ⟨rest, hrest⟩ : ∃ rest, exponent - 1 = rest + 1 :=
        ⟨exponent - 2, by omega⟩
      rw [hrest]
      simp [Nat.pow_succ, Nat.mul_comm]
    have relation :
        2 * embeddedValue returned =
          3 * (2 ^ exponent * embeddedValue source) - 2 := by
      omega
    rw [powerSplit, lowerPowerSplit] at relation
    obtain ⟨sourceHalf, sourceOdd⟩ := embeddedValue_odd source
    rw [sourceOdd] at relation ⊢
    rcases even_or_odd returned with ⟨half, rfl⟩ | ⟨half, rfl⟩
    · simp [embeddedValue_formula, Q, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] at relation ⊢
      omega
    · simp [embeddedValue_formula, Q, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] at relation ⊢
      omega
  · subst complementBit
    have powerSplit : 2 ^ exponent = 2 * 2 ^ (exponent - 1) := by
      obtain ⟨rest, rfl⟩ : ∃ rest, exponent = rest + 1 :=
        ⟨exponent - 1, by omega⟩
      simp [Nat.pow_succ, Nat.mul_comm]
    have lowerPowerSplit : 2 ^ (exponent - 1) =
        2 * 2 ^ (exponent - 2) := by
      obtain ⟨rest, hrest⟩ : ∃ rest, exponent - 1 = rest + 1 :=
        ⟨exponent - 2, by omega⟩
      rw [hrest]
      simp [Nat.pow_succ, Nat.mul_comm]
    have relation :
        2 * embeddedValue returned =
          3 * (2 ^ exponent * embeddedValue source) + 2 := by
      omega
    rw [powerSplit, lowerPowerSplit] at relation
    obtain ⟨sourceHalf, sourceOdd⟩ := embeddedValue_odd source
    rw [sourceOdd] at relation ⊢
    rcases even_or_odd returned with ⟨half, rfl⟩ | ⟨half, rfl⟩
    · simp [embeddedValue_formula, Q, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] at relation ⊢
      omega
    · simp [embeddedValue_formula, Q, Nat.mul_assoc, Nat.mul_left_comm,
        Nat.mul_comm] at relation ⊢
      omega

end ThreeNPlusMinusOne
