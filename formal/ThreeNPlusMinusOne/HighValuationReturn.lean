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
  have restShape : rest = exponent - 2 := by omega
  rw [restShape]
  simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

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
    simp [Nat.mul_assoc, Nat.mul_comm]
  have tailProductPositive : 0 < tailProduct := by
    rw [tailProductEquation]
    exact Nat.mul_pos (embeddedValue_positive source)
      (Nat.pow_pos (by omega))
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
