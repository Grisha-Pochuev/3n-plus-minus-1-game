import ThreeNPlusMinusOne.ConstantTailCoordinates
import ThreeNPlusMinusOne.Outcome
import ThreeNPlusMinusOne.Source

set_option autoImplicit false

/-!
# Reverse coefficient frame (Section 16)

This is the game-theoretic reverse descent which removes a factor of three
from a DRAW coefficient at exponent at least two.
-/

namespace ThreeNPlusMinusOne

private theorem Q_positive {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) (hexponent : 1 ≤ exponent) :
    0 < Q coefficient exponent tailBit := by
  exact IsConstantTail.state_positive
    ⟨positive, odd, hexponent, bit, rfl⟩

/--
If `Q_r^e(3c)` is DRAW for `r>=2`, one of the two reverse parents with
coefficient `c` is DRAW.
-/
theorem reverse_factor_three_draw
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) (hexponent : 2 ≤ exponent)
    (draw : Draw (Q (3 * coefficient) exponent tailBit)) :
    Draw (Q coefficient (exponent + 1) tailBit) ∨
      Draw (Q coefficient (exponent + 2) tailBit) := by
  classical
  let target := Q (3 * coefficient) exponent tailBit
  let firstParent := Q coefficient (exponent + 1) tailBit
  let secondParent := Q coefficient (exponent + 2) tailBit
  have oddTriple : OddNat (3 * coefficient) := by
    obtain ⟨k, rfl⟩ := odd
    exact ⟨3 * k + 1, by omega⟩
  have targetPositive : 0 < target :=
    Q_positive (by omega) oddTriple bit (by omega)
  have firstPositive : 0 < firstParent :=
    Q_positive positive odd bit (by omega)
  have secondPositive : 0 < secondParent :=
    Q_positive positive odd bit (by omega)
  have firstA : A firstParent = target := by
    dsimp only [firstParent, target]
    rw [A_Q positive bit (by omega)]
    congr 2
  have secondB : B secondParent = target := by
    dsimp only [secondParent, target]
    rw [B_Q positive bit (by omega)]
    congr 2
  by_cases firstDraw : Draw firstParent
  · exact Or.inl firstDraw
  by_cases secondDraw : Draw secondParent
  · exact Or.inr secondDraw
  have firstNotLosing : ¬ Losing firstParent := by
    intro firstLosing
    have children := firstLosing.children_winning firstPositive
    rw [firstA] at children
    exact draw.1 children.1
  have secondNotLosing : ¬ Losing secondParent := by
    intro secondLosing
    have children := secondLosing.children_winning secondPositive
    rw [secondB] at children
    exact draw.1 children.2
  have firstWinning : Winning firstParent :=
    winning_of_not_draw_and_not_losing firstDraw firstNotLosing
  have secondWinning : Winning secondParent :=
    winning_of_not_draw_and_not_losing secondDraw secondNotLosing
  have firstOtherLosing : Losing (B firstParent) := by
    apply firstWinning.B_losing_of_A_not_losing
    rw [firstA]
    exact draw.2
  have secondOtherLosing : Losing (A secondParent) := by
    apply secondWinning.A_losing_of_B_not_losing
    rw [secondB]
    exact draw.2
  have firstOther :
      B firstParent = Q (3 * coefficient) (exponent - 1) tailBit := by
    dsimp only [firstParent]
    rw [B_Q positive bit (by omega)]
    rw [show exponent + 1 - 2 = exponent - 1 by omega]
  have secondOther :
      A secondParent = Q (3 * coefficient) (exponent + 1) tailBit := by
    dsimp only [secondParent]
    rw [A_Q positive bit (by omega)]
    rw [show exponent + 2 - 1 = exponent + 1 by omega]
  have firstOtherPositive : 0 < B firstParent := by
    rw [firstOther]
    exact Q_positive (by omega) oddTriple bit (by omega)
  have secondOtherPositive : 0 < A secondParent := by
    rw [secondOther]
    exact Q_positive (by omega) oddTriple bit (by omega)
  have firstChildren :=
    firstOtherLosing.children_winning firstOtherPositive
  have secondChildren :=
    secondOtherLosing.children_winning secondOtherPositive
  have targetA : A target = B (A secondParent) := by
    rw [secondOther]
    dsimp only [target]
    rw [A_Q (by omega) bit (by omega)]
    rw [B_Q (by omega) bit (by omega)]
    rw [show exponent + 1 - 2 = exponent - 1 by omega]
  have targetAWinning : Winning (A target) := by
    rw [targetA]
    exact secondChildren.2
  have targetBWinning : Winning (B target) := by
    by_cases htwo : exponent = 2
    · subst exponent
      have boundary := B_Q_one_eq_two (by omega : 0 < 3 * coefficient)
        oddTriple bit
      have hfirst : B firstParent = Q (3 * coefficient) 1 tailBit := by
        simpa using firstOther
      rw [hfirst] at firstChildren
      dsimp only [target]
      rw [← boundary]
      exact firstChildren.2
    · have hthree : 3 ≤ exponent := by omega
      have targetB : B target = A (B firstParent) := by
        rw [firstOther]
        dsimp only [target]
        rw [B_Q (by omega) bit hthree]
        rw [A_Q (by omega) bit (by omega)]
        rw [show exponent - 1 - 1 = exponent - 2 by omega]
      rw [targetB]
      exact firstChildren.1
  have targetLosing : Losing target :=
    Losing.replies targetPositive targetAWinning targetBWinning
  exact False.elim (draw.2 targetLosing)

/--
All powers of three can be removed from a DRAW coefficient.  The tail
exponent may grow, but never decreases, so every recursive use remains in
the proven `exponent >= 2` regime.
-/
theorem reverse_all_three_factors_draw
    {coefficient factorExponent exponent tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) (hexponent : 2 ≤ exponent)
    (draw : Draw (Q (3 ^ factorExponent * coefficient) exponent tailBit)) :
    ∃ finalExponent,
      exponent ≤ finalExponent ∧
        Draw (Q coefficient finalExponent tailBit) := by
  induction factorExponent generalizing exponent with
  | zero =>
      exact ⟨exponent, Nat.le_refl exponent, by simpa using draw⟩
  | succ factorExponent ih =>
      have innerPositive : 0 < 3 ^ factorExponent * coefficient :=
        Nat.mul_pos (Nat.pow_pos (by omega)) positive
      have innerOdd : OddNat (3 ^ factorExponent * coefficient) :=
        (odd_three_pow factorExponent).mul odd
      have coefficientShape :
          3 ^ (factorExponent + 1) * coefficient =
            3 * (3 ^ factorExponent * coefficient) := by
        simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
      rw [coefficientShape] at draw
      have firstStep := reverse_factor_three_draw
        innerPositive innerOdd bit hexponent draw
      rcases firstStep with firstDraw | secondDraw
      · obtain ⟨finalExponent, finalLarge, finalDraw⟩ :=
          ih (exponent := exponent + 1) (by omega) firstDraw
        exact ⟨finalExponent, by omega, finalDraw⟩
      · obtain ⟨finalExponent, finalLarge, finalDraw⟩ :=
          ih (exponent := exponent + 2) (by omega) secondDraw
        exact ⟨finalExponent, by omega, finalDraw⟩

end ThreeNPlusMinusOne
