import ThreeNPlusMinusOne.ConstantTail
import ThreeNPlusMinusOne.Outcome

set_option autoImplicit false

/-!
# Constant-tail coefficient bounds (Section 15)
-/

namespace ThreeNPlusMinusOne

structure IsConstantTail
    (state coefficient exponent tailBit : Nat) : Prop where
  positive : 0 < coefficient
  odd : OddNat coefficient
  exponentPositive : 1 ≤ exponent
  bit : Bit tailBit
  equation : state = Q coefficient exponent tailBit

theorem IsConstantTail.state_positive
    {state coefficient exponent tailBit : Nat}
    (coordinates : IsConstantTail state coefficient exponent tailBit) :
    0 < state := by
  rcases coordinates.bit with rfl | rfl
  · rw [coordinates.equation]
    simp only [Q, Nat.sub_zero]
    exact Nat.mul_pos coordinates.positive (Nat.pow_pos (by decide))
  · rw [coordinates.equation]
    unfold Q
    have hexponent := coordinates.exponentPositive
    let base := coefficient * 2 ^ (exponent - 1)
    have hbase : 0 < base :=
      Nat.mul_pos coordinates.positive (Nat.pow_pos (by decide))
    have hsplit : coefficient * 2 ^ exponent = 2 * base := by
      obtain ⟨rest, rfl⟩ : ∃ rest, exponent = rest + 1 :=
        ⟨exponent - 1, by omega⟩
      simp [base, Nat.pow_succ, Nat.mul_comm,
        Nat.mul_left_comm]
    rw [hsplit]
    omega

/-- A raw constant-tail value divisible by four has tail exponent at least two. -/
theorem IsConstantTail.exponentAtLeastTwo_of_raw_divisible_by_four
    {state coefficient exponent tailBit quotient : Nat}
    (coordinates : IsConstantTail state coefficient exponent tailBit)
    (divisible : state + tailBit = 4 * quotient) :
    2 ≤ exponent := by
  by_cases large : 2 ≤ exponent
  · exact large
  · have small : exponent = 0 ∨ exponent = 1 := by omega
    obtain ⟨half, coefficientShape⟩ := coordinates.odd
    have equation := coordinates.equation
    rcases coordinates.bit with bitZero | bitOne <;>
      rcases small with exponentZero | exponentOne <;>
      subst tailBit <;> subst exponent <;>
      simp [Q] at equation divisible <;> omega

/-- Any positive constant-tail representation has coefficient at most `(q+1)/2`. -/
theorem IsConstantTail.coefficient_le_half
    {state coefficient exponent tailBit : Nat}
    (coordinates : IsConstantTail state coefficient exponent tailBit) :
    coefficient ≤ (state + 1) / 2 := by
  have hexponent := coordinates.exponentPositive
  have hsplit : 2 ^ exponent = 2 * 2 ^ (exponent - 1) := by
    obtain ⟨rest, rfl⟩ : ∃ rest, exponent = rest + 1 :=
      ⟨exponent - 1, by omega⟩
    simp [Nat.pow_succ, Nat.mul_comm]
  have hbase : 0 < coefficient * 2 ^ (exponent - 1) :=
    Nat.mul_pos coordinates.positive (Nat.pow_pos (by decide))
  have hcoefficientBase :
      coefficient ≤ coefficient * 2 ^ (exponent - 1) := by
    calc
      coefficient = coefficient * 1 := by simp
      _ ≤ coefficient * 2 ^ (exponent - 1) :=
        Nat.mul_le_mul_left coefficient (by
          have hpositive : 0 < 2 ^ (exponent - 1) := Nat.pow_pos (by decide)
          omega)
  rcases coordinates.bit with rfl | rfl
  · rw [coordinates.equation]
    simp only [Q, Nat.sub_zero]
    rw [hsplit]
    have hshape : coefficient * (2 * 2 ^ (exponent - 1)) =
        2 * (coefficient * 2 ^ (exponent - 1)) := by
      simp [Nat.mul_left_comm]
    rw [hshape]
    omega
  · rw [coordinates.equation]
    unfold Q
    rw [hsplit]
    have hshape : coefficient * (2 * 2 ^ (exponent - 1)) =
        2 * (coefficient * 2 ^ (exponent - 1)) := by
      simp [Nat.mul_left_comm]
    rw [hshape]
    omega

def boundaryChild (coefficient tailBit : Nat) : Nat :=
  R (3 * coefficient - tailBit)

theorem B_Q_one_eq_boundaryChild {coefficient tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit) :
    B (Q coefficient 1 tailBit) = boundaryChild coefficient tailBit := by
  unfold B boundaryChild
  rw [A_Q positive bit (by omega : 1 ≤ 1)]
  rcases bit with rfl | rfl <;> simp [Q]

theorem B_Q_two_eq_boundaryChild {coefficient tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) :
    B (Q coefficient 2 tailBit) = boundaryChild coefficient tailBit := by
  rw [← B_Q_one_eq_two positive odd bit]
  exact B_Q_one_eq_boundaryChild positive bit

/-- Section 15's universal coefficient bound at the common B-boundary. -/
theorem boundaryChild_coefficient_bound
    {coefficient tailBit child childCoefficient childExponent childBit : Nat}
    (odd : OddNat coefficient) (bit : Bit tailBit)
    (childEquation : child = boundaryChild coefficient tailBit)
    (childCoordinates :
      IsConstantTail child childCoefficient childExponent childBit) :
    childCoefficient ≤ (3 * coefficient + 1) / 4 := by
  have hcoefficient := childCoordinates.coefficient_le_half
  have hR := R_le_half (3 * coefficient - tailBit)
  have hodd : coefficient % 2 = 1 := by
    obtain ⟨k, rfl⟩ := odd
    omega
  rw [childEquation, boundaryChild] at hcoefficient
  rcases bit with rfl | rfl
  · simp only [Nat.sub_zero] at hcoefficient hR ⊢
    omega
  · omega

/-- Away from the resolved coefficient `1`, the boundary coefficient is strict. -/
theorem boundaryChild_coefficient_strict
    {coefficient tailBit child childCoefficient childExponent childBit : Nat}
    (coefficientLarge : 3 ≤ coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit)
    (childEquation : child = boundaryChild coefficient tailBit)
    (childCoordinates :
      IsConstantTail child childCoefficient childExponent childBit) :
    childCoefficient < coefficient := by
  have hbound := boundaryChild_coefficient_bound odd bit childEquation childCoordinates
  omega

/--
Game-theoretic Section 15 boundary step.  At a globally minimum DRAW
coefficient, the common B-child is winning and the A-child remains DRAW.
-/
theorem minimumCoefficient_boundary_forces_A
    {coefficient exponent tailBit child childCoefficient childExponent childBit : Nat}
    (coefficientLarge : 3 ≤ coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) (boundaryExponent : exponent = 1 ∨ exponent = 2)
    (parentDraw : Draw (Q coefficient exponent tailBit))
    (childEquation : child = boundaryChild coefficient tailBit)
    (childCoordinates :
      IsConstantTail child childCoefficient childExponent childBit)
    (minimum :
      ∀ {state candidateCoefficient candidateExponent candidateBit},
        IsConstantTail state candidateCoefficient candidateExponent candidateBit →
        Draw state → coefficient ≤ candidateCoefficient) :
    Winning child ∧ Draw (A (Q coefficient exponent tailBit)) := by
  have childStrict : childCoefficient < coefficient :=
    boundaryChild_coefficient_strict coefficientLarge odd bit
      childEquation childCoordinates
  have childNotDraw : ¬ Draw child := by
    intro childDraw
    have := minimum childCoordinates childDraw
    omega
  have coefficientPositive : 0 < coefficient := by omega
  have hB : B (Q coefficient exponent tailBit) = child := by
    rcases boundaryExponent with rfl | rfl
    · exact (B_Q_one_eq_boundaryChild coefficientPositive bit).trans childEquation.symm
    · exact (B_Q_two_eq_boundaryChild coefficientPositive odd bit).trans childEquation.symm
  have childNotLosing : ¬ Losing child := by
    rw [← hB]
    exact parentDraw.children_not_losing.2
  have childWinning := winning_of_not_draw_and_not_losing
    childNotDraw childNotLosing
  constructor
  · exact childWinning
  · apply parentDraw.A_of_B_winning
    rw [hB]
    exact childWinning

end ThreeNPlusMinusOne
