import ThreeNPlusMinusOne.HighValuationHeight
import ThreeNPlusMinusOne.TransferBound

set_option autoImplicit false

/-!
# Phase selection after the high-valuation return (Section 35)

This file records the arithmetic phase geometry needed at the start of
Section 35 and preserves a supplied `DRAW` carrier through its exact
obligation form.  It does not derive the high-return valuation-two premise
from the preceding signed equations; that outcome-routing step is still open.
-/

namespace ThreeNPlusMinusOne

/-- An exponent-one constant-tail state with odd coefficient selects its
tail bit.  This is the `v=4` phase calculation for the returned side `Z`. -/
theorem sourceASelectingBit_Q_one_of_odd
    {coefficient tailBit : Nat}
    (odd : OddNat coefficient) (bit : Bit tailBit) :
    sourceASelectingBit (Q coefficient 1 tailBit) = tailBit := by
  obtain ⟨half, coefficientShape⟩ := odd
  rcases bit with tailZero | tailOne
  · rw [tailZero, coefficientShape]
    simp [sourceASelectingBit, Q] <;> omega
  · rw [tailOne, coefficientShape]
    simp [sourceASelectingBit, Q] <;> omega

/-- A constant-tail state with at least two tail bits selects the opposite
phase.  This is the `v≥5` phase calculation for the returned side `Z`. -/
theorem sourceASelectingBit_Q_long
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 2 ≤ exponent) :
    sourceASelectingBit (Q coefficient exponent tailBit) = 1 - tailBit := by
  have powerSplit : 2 ^ exponent = 4 * 2 ^ (exponent - 2) := by
    obtain ⟨rest, restShape⟩ : ∃ rest, exponent = rest + 2 :=
      ⟨exponent - 2, by omega⟩
    rw [restShape]
    simp [Nat.pow_add, Nat.mul_comm]
  let base := coefficient * 2 ^ (exponent - 2)
  have basePositive : 0 < base := by
    dsimp [base]
    exact Nat.mul_pos positive (Nat.pow_pos (by omega))
  rcases bit with tailZero | tailOne
  · rw [tailZero]
    have stateShape : Q coefficient exponent 0 = 4 * base := by
      simp [Q, powerSplit, base, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    rw [stateShape]
    simpa using sourceASelectingBit_four_mul base
  · rw [tailOne]
    have stateShape : Q coefficient exponent 1 = 4 * base - 1 := by
      simp [Q, powerSplit, base, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    rw [stateShape]
    simpa using sourceASelectingBit_four_mul_sub_one basePositive

/-- The least bit of every positive constant-tail coordinate is its declared
tail bit. -/
theorem Q_mod_two
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentPositive : 1 ≤ exponent) :
    Q coefficient exponent tailBit % 2 = tailBit := by
  have powerSplit : 2 ^ exponent = 2 * 2 ^ (exponent - 1) := by
    obtain ⟨rest, restShape⟩ : ∃ rest, exponent = rest + 1 :=
      ⟨exponent - 1, by omega⟩
    rw [restShape]
    simp [Nat.pow_succ, Nat.mul_comm]
  let base := coefficient * 2 ^ (exponent - 1)
  have basePositive : 0 < base := by
    dsimp [base]
    exact Nat.mul_pos positive (Nat.pow_pos (by omega))
  rcases bit with tailZero | tailOne
  · rw [tailZero]
    have stateShape : Q coefficient exponent 0 = 2 * base := by
      simp [Q, powerSplit, base, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    rw [stateShape]
    omega
  · rw [tailOne]
    have stateShape : Q coefficient exponent 1 = 2 * base - 1 := by
      simp [Q, powerSplit, base, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    rw [stateShape]
    omega

/-- In the boundary `v=4` case, the returned contracting side has selecting
bit `e`; hence its Section 35 obligation phase is the B-selecting complement
`1-e`. -/
theorem highReturn_boundary_contracting_phase
    {coefficient tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) :
    sourceASelectingBit (B (Q coefficient 3 tailBit)) = tailBit := by
  rw [B_Q positive bit (by omega : 3 ≤ 3)]
  apply sourceASelectingBit_Q_one_of_odd
  · obtain ⟨half, coefficientShape⟩ := odd
    exact ⟨3 * half + 1, by omega⟩
  · exact bit

/-- In every long `v≥5` case, the returned contracting side has selecting
bit `1-e`; hence its Section 35 obligation phase `1-e` selects its A-child. -/
theorem highReturn_long_contracting_phase
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 5 ≤ exponent) :
    sourceASelectingBit (B (Q coefficient (exponent - 1) tailBit)) =
      1 - tailBit := by
  rw [highReturn_contracting_child positive bit (by omega)]
  exact sourceASelectingBit_Q_long (by omega) bit (by omega)

/-- In the `v=4` boundary case, the B-child selected by the complement phase
of the returned side is exactly the lower Section 34 occurrence. -/
theorem highReturn_boundary_selected_child
    {coefficient tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) :
    B (B (Q coefficient 3 tailBit)) =
      B (A (Q coefficient 3 tailBit)) := by
  exact (highReturn_boundary_common_grandchild positive odd bit).symm

/-- In every `v≥5` long case, the A-child selected by the returned-side phase
is exactly the lower Section 34 occurrence. -/
theorem highReturn_long_selected_child
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 5 ≤ exponent) :
    A (B (Q coefficient (exponent - 1) tailBit)) =
      B (A (Q coefficient (exponent - 1) tailBit)) := by
  exact (highReturn_long_common_grandchild positive bit exponentLarge).symm

/-- An exact valuation-two signed transition from a real DRAW parent packages
its two exact children as the Section 27 obligation over the returned source.
This retains the actual DRAW carrier rather than replacing it with a bare
coordinate identity. -/
theorem drawObligation_of_signed_valuation_two
    {parent source phase : Nat}
    (parentDraw : Draw parent)
    (tail : IsConstantTail (A parent) (embeddedValue source) 2 phase) :
    DrawObligation source phase := by
  dsimp [DrawObligation]
  right
  refine ⟨parent, parentDraw, Or.inl ⟨tail.equation, ?_⟩⟩
  unfold B
  rw [tail.equation]
  exact R_Q tail.positive tail.bit (by omega : 2 ≤ 2)

namespace DrawObligation

/-- Every obligation retains a concrete DRAW carrier at one of its two lift
members.  In the parent-entry form this follows by taking one DRAW child of
the retained parent. -/
theorem has_draw_lift
    {source phase : Nat} (obligation : DrawObligation source phase) :
    Draw (Q (embeddedValue source) 1 phase) ∨
      Draw (Q (embeddedValue source) 2 phase) := by
  dsimp [DrawObligation] at obligation
  rcases obligation with lowerDraw | parentEntry
  · exact Or.inl lowerDraw
  · rcases parentEntry with ⟨parent, parentDraw, parentChildren⟩
    obtain ⟨next, move, nextDraw⟩ := parentDraw.has_draw_child
    rcases parentChildren with order | order
    · rcases move.2 with nextA | nextB
      · rw [nextA, order.1] at nextDraw
        exact Or.inr nextDraw
      · rw [nextB, order.2] at nextDraw
        exact Or.inl nextDraw
    · rcases move.2 with nextA | nextB
      · rw [nextA, order.1] at nextDraw
        exact Or.inl nextDraw
      · rw [nextB, order.2] at nextDraw
        exact Or.inr nextDraw

/-- If both lift members have the same contracting child `target` and that
child is WIN, an obligation supplies an actual DRAW-to-WIN boundary ending at
`target`. -/
theorem draw_to_winning_boundary
    {source phase target : Nat}
    (obligation : DrawObligation source phase)
    (lowerSide : B (Q (embeddedValue source) 1 phase) = target)
    (upperSide : B (Q (embeddedValue source) 2 phase) = target)
    (targetWinning : Winning target) :
    ∃ drawLift,
      Draw drawLift ∧ B drawLift = target ∧ Winning target := by
  rcases has_draw_lift obligation with lowerDraw | upperDraw
  · exact ⟨Q (embeddedValue source) 1 phase,
      lowerDraw, lowerSide, targetWinning⟩
  · exact ⟨Q (embeddedValue source) 2 phase,
      upperDraw, upperSide, targetWinning⟩

end DrawObligation

/-- In an A-selecting obligation, the Section 24 parity guard makes the two
lift members share the ordinary child `B(A(source))`. -/
theorem selectedObligation_shared_B_child
    {source : Nat}
    (parity : A (A source) % 2 ≠ sourceASelectingBit source) :
    B (Q (embeddedValue source) 1 (sourceASelectingBit source)) =
        B (A source) ∧
      B (Q (embeddedValue source) 2 (sourceASelectingBit source)) =
        B (A source) := by
  have lowerSide := selectedLift_side_eq_B parity
  have phaseBit := sourceASelectingBit_is_bit source
  constructor
  · exact lowerSide
  · calc
      B (Q (embeddedValue source) 2 (sourceASelectingBit source)) =
          B (Q (embeddedValue source) 1 (sourceASelectingBit source)) :=
        (B_Q_one_eq_two (embeddedValue_positive source)
          (embeddedValue_odd source) phaseBit).symm
      _ = B (A source) := lowerSide

/-- The outcome form of Section 35's nonexceptional A-selecting transfer.
Under its parity guard, an obligation and a WIN witness for `B(A(source))`
produce a concrete DRAW-to-WIN boundary at that common child. -/
theorem selectedObligation_draw_to_winning_boundary
    {source : Nat}
    (obligation : DrawObligation source (sourceASelectingBit source))
    (parity : A (A source) % 2 ≠ sourceASelectingBit source)
    (targetWinning : Winning (B (A source))) :
    ∃ drawLift,
      Draw drawLift ∧ B drawLift = B (A source) ∧ Winning (B (A source)) := by
  have shared := selectedObligation_shared_B_child parity
  exact DrawObligation.draw_to_winning_boundary obligation shared.1 shared.2
    targetWinning

/-- The Section 24 parity guard required after a high-valuation return holds
uniformly once `v≥6`: the next expansion of the selected `Z` child has tail
bit `e`, whereas `Z` selects phase `1-e`. -/
theorem highReturn_long_AA_parity_guard
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 6 ≤ exponent) :
    A (A (B (Q coefficient (exponent - 1) tailBit))) % 2 ≠
      sourceASelectingBit (B (Q coefficient (exponent - 1) tailBit)) := by
  have contractingPhase := highReturn_long_contracting_phase positive bit
    (by omega : 5 ≤ exponent)
  have contractingChild := highReturn_contracting_child positive bit
    (by omega : 4 ≤ exponent)
  have expandingChild :
      A (B (Q coefficient (exponent - 1) tailBit)) =
        Q (9 * coefficient) (exponent - 4) tailBit := by
    rw [contractingChild]
    exact (highReturn_common_child_long positive bit
      (by omega : 5 ≤ exponent)).2
  have secondExpansion :
      A (A (B (Q coefficient (exponent - 1) tailBit))) =
        Q (27 * coefficient) (exponent - 5) tailBit := by
    rw [expandingChild]
    simpa [show 3 * (9 * coefficient) = 27 * coefficient by omega,
      show exponent - 4 - 1 = exponent - 5 by omega] using
      A_Q (by omega : 0 < 9 * coefficient) bit
        (by omega : 1 ≤ exponent - 4)
  have expansionParity :
      A (A (B (Q coefficient (exponent - 1) tailBit))) % 2 = tailBit := by
    rw [secondExpansion]
    exact Q_mod_two (by omega : 0 < 27 * coefficient) bit
      (by omega : 1 ≤ exponent - 5)
  rw [expansionParity, contractingPhase]
  rcases bit with tailZero | tailOne <;> omega

/-- Conditional nonexceptional Section 35 transfer.  For every `v≥6`, once
the exact returned `DRAW` obligation and its common-child WIN witness are
supplied, it yields a concrete DRAW-to-WIN boundary at that child. -/
theorem highReturn_long_draw_to_winning_boundary
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 6 ≤ exponent)
    (obligation :
      DrawObligation (B (Q coefficient (exponent - 1) tailBit))
        (1 - tailBit))
    (targetWinning :
      Winning (B (A (B (Q coefficient (exponent - 1) tailBit))))) :
    ∃ drawLift,
      Draw drawLift ∧
        B drawLift = B (A (B (Q coefficient (exponent - 1) tailBit))) ∧
        Winning (B (A (B (Q coefficient (exponent - 1) tailBit)))) := by
  have contractingPhase := highReturn_long_contracting_phase positive bit
    (by omega : 5 ≤ exponent)
  rw [← contractingPhase] at obligation
  exact selectedObligation_draw_to_winning_boundary obligation
    (highReturn_long_AA_parity_guard positive bit exponentLarge)
    targetWinning

end ThreeNPlusMinusOne
