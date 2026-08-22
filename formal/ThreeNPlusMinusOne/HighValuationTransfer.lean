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
      simp [Q, powerSplit, base, Nat.mul_assoc, Nat.mul_comm]
    rw [stateShape]
    simpa using sourceASelectingBit_four_mul base
  · rw [tailOne]
    have stateShape : Q coefficient exponent 1 = 4 * base - 1 := by
      simp [Q, powerSplit, base, Nat.mul_assoc, Nat.mul_comm]
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
      simp [Q, powerSplit, base, Nat.mul_left_comm]
    rw [stateShape]
    omega
  · rw [tailOne]
    have stateShape : Q coefficient exponent 1 = 2 * base - 1 := by
      simp [Q, powerSplit, base, Nat.mul_left_comm]
    rw [stateShape]
    omega

/-- The exact Section 33 return coordinate is an actual constant-tail
certificate, not merely an equality of natural numbers. -/
theorem exponentThree_return_constantTail_from_valuations
    {side returned source exponent tailBit tailProduct : Nat}
    (bit : Bit tailBit)
    (exponentLarge : 4 ≤ exponent)
    (tailProductEquation :
      tailProduct = embeddedValue source * 2 ^ (exponent - 1))
    (firstValuation :
      9 * embeddedValue side + 1 - 2 * tailBit =
        2 ^ exponent * embeddedValue source)
    (returnValuation :
      27 * embeddedValue side + 1 - 2 * tailBit =
        2 * embeddedValue returned) :
    IsConstantTail returned (embeddedValue source) (exponent - 1)
      (1 - tailBit) := by
  refine ⟨embeddedValue_positive source, embeddedValue_odd source, by omega,
    ?_, ?_⟩
  · rcases bit with tailZero | tailOne
    · rw [tailZero]
      exact Or.inr (by omega)
    · rw [tailOne]
      exact Or.inl (by omega)
  · exact exponentThree_return_Q_coordinate_from_valuations bit
      (by omega) tailProductEquation firstValuation returnValuation

/-- Transporting the Section 33 returned coordinate through its contracting
child yields the precise lower constant-tail certificate used as the returned
side in Sections 34--35. -/
theorem highReturn_contracting_constantTail
    {source returned exponent tailBit : Nat}
    (bit : Bit tailBit) (exponentLarge : 4 ≤ exponent)
    (coordinate :
      returned = Q (embeddedValue source) (exponent - 1) (1 - tailBit)) :
    IsConstantTail (B returned) (3 * embeddedValue source) (exponent - 3)
      (1 - tailBit) := by
  have complementBit : Bit (1 - tailBit) := by
    rcases bit with tailZero | tailOne
    · rw [tailZero]
      exact Or.inr (by omega)
    · rw [tailOne]
      exact Or.inl (by omega)
  have tripleOdd : OddNat (3 * embeddedValue source) := by
    obtain ⟨half, halfShape⟩ := embeddedValue_odd source
    exact ⟨3 * half + 1, by rw [halfShape]; omega⟩
  refine ⟨Nat.mul_pos (by omega) (embeddedValue_positive source), tripleOdd,
    by omega, complementBit, ?_⟩
  rw [coordinate]
  exact highReturn_contracting_child (embeddedValue_positive source)
    complementBit exponentLarge

/-- The preceding two bridges compose: the concrete signed valuations yield
the contracting-side constant-tail certificate directly. -/
theorem exponentThree_return_contracting_constantTail_from_valuations
    {side returned source exponent tailBit tailProduct : Nat}
    (bit : Bit tailBit)
    (exponentLarge : 4 ≤ exponent)
    (tailProductEquation :
      tailProduct = embeddedValue source * 2 ^ (exponent - 1))
    (firstValuation :
      9 * embeddedValue side + 1 - 2 * tailBit =
        2 ^ exponent * embeddedValue source)
    (returnValuation :
      27 * embeddedValue side + 1 - 2 * tailBit =
        2 * embeddedValue returned) :
    IsConstantTail (B returned) (3 * embeddedValue source) (exponent - 3)
      (1 - tailBit) := by
  apply highReturn_contracting_constantTail bit exponentLarge
  exact exponentThree_return_Q_coordinate_from_valuations bit
    (by omega) tailProductEquation firstValuation returnValuation

/-- The B-selecting lift at the returned Section 33 source has exact
valuation two.  This is the arithmetic input needed to turn an actual DRAW
carrier at that lift into the Section 35 obligation over its B-child. -/
theorem highReturn_bSelecting_valuation_two
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 4 ≤ exponent) :
    BSelectingValuationTwo (Q coefficient (exponent - 1) tailBit) := by
  have selectingPhase :
      sourceASelectingBit (Q coefficient (exponent - 1) tailBit) =
        1 - tailBit :=
    sourceASelectingBit_Q_long positive bit (by omega : 2 ≤ exponent - 1)
  have doubleComplement : 1 - (1 - tailBit) = tailBit := by
    rcases bit with tailZero | tailOne <;> omega
  have returnedChild := highReturn_contracting_child positive bit exponentLarge
  have returnedEmbedded :
      embeddedValue (Q coefficient (exponent - 1) tailBit) =
        2 * Q (3 * coefficient) (exponent - 2) tailBit + 1 := by
    unfold embeddedValue
    simpa only [show exponent - 1 - 1 = exponent - 2 by omega] using
      congrArg (fun value => 2 * value + 1)
        (A_Q positive bit (by omega : 1 ≤ exponent - 1))
  have childEmbedded :
      embeddedValue (B (Q coefficient (exponent - 1) tailBit)) =
        2 * Q (9 * coefficient) (exponent - 4) tailBit + 1 := by
    rw [returnedChild]
    unfold embeddedValue
    simpa [show 3 * (3 * coefficient) = 9 * coefficient by omega,
      show exponent - 3 - 1 = exponent - 4 by omega] using
      congrArg (fun value => 2 * value)
        (A_Q (by omega : 0 < 3 * coefficient) bit
          (by omega : 1 ≤ exponent - 3))
  have powerSplit : 2 ^ (exponent - 2) = 4 * 2 ^ (exponent - 4) := by
    obtain ⟨rest, restShape⟩ : ∃ rest, exponent - 2 = rest + 2 :=
      ⟨exponent - 4, by omega⟩
    rw [restShape]
    have restEquation : rest = exponent - 4 := by omega
    rw [restEquation]
    simp [Nat.pow_add, Nat.mul_comm]
  let base := coefficient * 2 ^ (exponent - 4)
  have basePositive : 0 < base := by
    dsimp [base]
    exact Nat.mul_pos positive (Nat.pow_pos (by omega))
  have returnedProduct :
      (3 * coefficient) * 2 ^ (exponent - 2) = 12 * base := by
    rw [powerSplit]
    calc
      (3 * coefficient) * (4 * 2 ^ (exponent - 4)) =
          (3 * 4) * (coefficient * 2 ^ (exponent - 4)) := by ac_rfl
      _ = 12 * base := by simp [base]
  have childProduct :
      (9 * coefficient) * 2 ^ (exponent - 4) = 9 * base := by
    dsimp [base]
    ac_rfl
  have returnedZero :
      Q (3 * coefficient) (exponent - 2) 0 = 12 * base := by
    simp only [Q, Nat.sub_zero]
    exact returnedProduct
  have returnedOne :
      Q (3 * coefficient) (exponent - 2) 1 = 12 * base - 1 := by
    unfold Q
    rw [returnedProduct]
  have childZero :
      Q (9 * coefficient) (exponent - 4) 0 = 9 * base := by
    simp only [Q, Nat.sub_zero]
    exact childProduct
  have childOne :
      Q (9 * coefficient) (exponent - 4) 1 = 9 * base - 1 := by
    unfold Q
    rw [childProduct]
  have valuation :
      3 * embeddedValue (Q coefficient (exponent - 1) tailBit) + 1 -
          2 * tailBit =
        2 ^ 2 * embeddedValue (B (Q coefficient (exponent - 1) tailBit)) := by
    rw [returnedEmbedded, childEmbedded]
    rcases bit with tailZero | tailOne
    · subst tailBit
      rw [returnedZero, childZero]
      omega
    · subst tailBit
      rw [returnedOne, childOne]
      omega
  unfold BSelectingValuationTwo
  rw [selectingPhase, doubleComplement]
  exact signedTransition_tail (embeddedValue_positive _)
    (embeddedValue_positive _) (embeddedValue_odd _) bit (by omega) valuation

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

/-- The omitted short-long case `v=5` is a genuine exceptional phase: when
the returned coefficient is odd, the next two expansions of its contracting
side have exactly the A-selecting phase, rather than the complementary phase
required by the Section 24 transfer. -/
theorem highReturn_v5_AA_parity_exception
    {coefficient tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) :
    A (A (B (Q coefficient 4 tailBit))) % 2 =
      sourceASelectingBit (B (Q coefficient 4 tailBit)) := by
  have contractingChild := highReturn_contracting_child positive bit
    (by omega : 4 ≤ 5)
  have firstExpansion :
      A (B (Q coefficient 4 tailBit)) = Q (9 * coefficient) 1 tailBit := by
    rw [contractingChild]
    simpa [show 3 * (3 * coefficient) = 9 * coefficient by omega] using
      A_Q (by omega : 0 < 3 * coefficient) bit (by omega : 1 ≤ 2)
  have secondExpansion :
      A (A (B (Q coefficient 4 tailBit))) = Q (27 * coefficient) 0 tailBit := by
    rw [firstExpansion]
    simpa [show 3 * (9 * coefficient) = 27 * coefficient by omega] using
      A_Q (by omega : 0 < 9 * coefficient) bit (by omega : 1 ≤ 1)
  have contractingPhase := highReturn_long_contracting_phase positive bit
    (by omega : 5 ≤ 5)
  rw [secondExpansion, contractingPhase]
  obtain ⟨half, coefficientShape⟩ := odd
  rcases bit with tailZero | tailOne
  · rw [tailZero, coefficientShape]
    simp [Q] <;> omega
  · rw [tailOne, coefficientShape]
    simp [Q] <;> omega

/-- A `WIN` tree whose `A` child is already known to be `WIN` must select its
`B` child.  Either child of that selected LOSS reply is consequently a WIN
occurrence at least two proof levels lower. -/
theorem WinningTree.twoLevelDrop_of_A_winning
    {state common height : Nat}
    (tree : WinningTree state height) (siblingWinning : Winning (A state))
    (selectedChildPositive : 0 < B state)
    (commonEquation : common = A (B state) ∨ common = B (B state)) :
    ∃ commonHeight, WinningTree common commonHeight ∧
      commonHeight + 2 ≤ height := by
  cases tree with
  | moveA _ reply =>
      apply False.elim
      exact siblingWinning.not_losing ⟨_, reply⟩
  | moveB nonterminal reply =>
      have replyOutcome : Losing (B state) := ⟨_, reply⟩
      have commonWinning : Winning common := by
        rcases commonEquation with commonA | commonB
        · rw [commonA]
          exact (replyOutcome.children_winning selectedChildPositive).1
        · rw [commonB]
          exact (replyOutcome.children_winning selectedChildPositive).2
      have commonPositive : 0 < common := by
        by_cases commonZero : common = 0
        · apply False.elim
          apply commonWinning.not_losing
          rw [commonZero]
          exact terminal_losing
        · omega
      obtain ⟨commonHeight, commonTree, lower⟩ :=
        reply.positive_child_lower commonPositive commonEquation
      exact ⟨commonHeight, commonTree, by omega⟩

/-- At the short nonexceptional boundary `v=6`, the common side
`B(A(Z))` is the contracting child of the LOSS sibling `B(Z)`. -/
theorem highReturn_v6_common_side_child
    {coefficient tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) :
    B (A (B (Q coefficient 5 tailBit))) =
      B (B (B (Q coefficient 5 tailBit))) := by
  have contractingChild := highReturn_contracting_child positive bit
    (by omega : 4 ≤ 6)
  have ninePositive : 0 < 9 * coefficient := by omega
  have nineOdd : OddNat (9 * coefficient) := by
    obtain ⟨half, coefficientShape⟩ := odd
    exact ⟨9 * half + 4, by rw [coefficientShape]; omega⟩
  calc
    B (A (B (Q coefficient 5 tailBit))) =
        B (A (Q (3 * coefficient) 3 tailBit)) := by
      exact congrArg (fun value => B (A value)) contractingChild
    _ = B (Q (9 * coefficient) 2 tailBit) := by
      simpa [show 3 * (3 * coefficient) = 9 * coefficient by omega] using
        congrArg B (A_Q (by omega : 0 < 3 * coefficient) bit
          (by omega : 1 ≤ 3))
    _ = B (Q (9 * coefficient) 1 tailBit) := by
      exact (B_Q_one_eq_two ninePositive nineOdd bit).symm
    _ = B (B (Q (3 * coefficient) 3 tailBit)) := by
      exact congrArg B (by
        simpa [show 3 * (3 * coefficient) = 9 * coefficient by omega] using
          (B_Q (by omega : 0 < 3 * coefficient) bit
            (by omega : 3 ≤ 3)).symm)
    _ = B (B (B (Q coefficient 5 tailBit))) := by
      exact congrArg B (congrArg B contractingChild.symm)

/-- Beyond `v=6`, the same common side is the expanding child of the LOSS
sibling `B(Z)`. -/
theorem highReturn_v_ge7_common_side_child
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 7 ≤ exponent) :
    B (A (B (Q coefficient (exponent - 1) tailBit))) =
      A (B (B (Q coefficient (exponent - 1) tailBit))) := by
  have contractingChild := highReturn_contracting_child positive bit
    (by omega : 4 ≤ exponent)
  have returnedGrandchild :
      B (B (Q coefficient (exponent - 1) tailBit)) =
        Q (9 * coefficient) (exponent - 5) tailBit := by
    calc
      B (B (Q coefficient (exponent - 1) tailBit)) =
          B (Q (3 * coefficient) (exponent - 3) tailBit) :=
        congrArg B contractingChild
      _ = Q (9 * coefficient) (exponent - 5) tailBit := by
        simpa [show 3 * (3 * coefficient) = 9 * coefficient by omega,
          show exponent - 3 - 2 = exponent - 5 by omega] using
          B_Q (by omega : 0 < 3 * coefficient) bit
            (by omega : 3 ≤ exponent - 3)
  calc
    B (A (B (Q coefficient (exponent - 1) tailBit))) =
        B (A (Q (3 * coefficient) (exponent - 3) tailBit)) := by
      exact congrArg (fun value => B (A value)) contractingChild
    _ = B (Q (9 * coefficient) (exponent - 4) tailBit) := by
      simpa [show 3 * (3 * coefficient) = 9 * coefficient by omega,
        show exponent - 3 - 1 = exponent - 4 by omega] using
        congrArg B (A_Q (by omega : 0 < 3 * coefficient) bit
          (by omega : 1 ≤ exponent - 3))
    _ = Q (27 * coefficient) (exponent - 6) tailBit := by
      simpa [show 3 * (9 * coefficient) = 27 * coefficient by omega,
        show exponent - 4 - 2 = exponent - 6 by omega] using
        B_Q (by omega : 0 < 9 * coefficient) bit
          (by omega : 3 ≤ exponent - 4)
    _ = A (Q (9 * coefficient) (exponent - 5) tailBit) := by
      symm
      simpa [show 3 * (9 * coefficient) = 27 * coefficient by omega,
        show exponent - 5 - 1 = exponent - 6 by omega] using
        A_Q (by omega : 0 < 9 * coefficient) bit
          (by omega : 1 ≤ exponent - 5)
    _ = A (B (B (Q coefficient (exponent - 1) tailBit))) := by
      exact congrArg A returnedGrandchild.symm

/-- The selected LOSS sibling of the returned contracting side is nonterminal
throughout the `v≥6` range. -/
theorem highReturn_long_loss_sibling_positive
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) (exponentLarge : 6 ≤ exponent) :
    0 < B (B (Q coefficient (exponent - 1) tailBit)) := by
  have contractingChild := highReturn_contracting_child positive bit
    (by omega : 4 ≤ exponent)
  have returnedGrandchild :
      B (B (Q coefficient (exponent - 1) tailBit)) =
        Q (9 * coefficient) (exponent - 5) tailBit := by
    calc
      B (B (Q coefficient (exponent - 1) tailBit)) =
          B (Q (3 * coefficient) (exponent - 3) tailBit) :=
        congrArg B contractingChild
      _ = Q (9 * coefficient) (exponent - 5) tailBit := by
        simpa [show 3 * (3 * coefficient) = 9 * coefficient by omega,
          show exponent - 3 - 2 = exponent - 5 by omega] using
          B_Q (by omega : 0 < 3 * coefficient) bit
            (by omega : 3 ≤ exponent - 3)
  have nineOdd : OddNat (9 * coefficient) := by
    obtain ⟨half, coefficientShape⟩ := odd
    exact ⟨9 * half + 4, by rw [coefficientShape]; omega⟩
  have coordinates :
      IsConstantTail (Q (9 * coefficient) (exponent - 5) tailBit)
        (9 * coefficient) (exponent - 5) tailBit :=
    ⟨by omega, nineOdd, by omega, bit, rfl⟩
  rw [returnedGrandchild]
  exact coordinates.state_positive

/-- The Section 35 common side has a concrete WIN tree two levels below a
given returned-side tree, provided the Section 34 selected child is WIN.
The `v=6` and `v≥7` child orientations are handled explicitly. -/
theorem highReturn_long_common_side_height_drop
    {coefficient exponent tailBit height : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) (exponentLarge : 6 ≤ exponent)
    (tree : WinningTree (B (Q coefficient (exponent - 1) tailBit)) height)
    (selectedWinning : Winning (A (B (Q coefficient (exponent - 1) tailBit)))) :
    ∃ commonHeight,
      WinningTree (B (A (B (Q coefficient (exponent - 1) tailBit))))
        commonHeight ∧ commonHeight + 2 ≤ height := by
  by_cases boundary : exponent = 6
  · subst exponent
    apply WinningTree.twoLevelDrop_of_A_winning tree selectedWinning
      (highReturn_long_loss_sibling_positive positive odd bit (by omega))
    right
    exact highReturn_v6_common_side_child positive odd bit
  · have longRange : 7 ≤ exponent := by omega
    apply WinningTree.twoLevelDrop_of_A_winning tree selectedWinning
      (highReturn_long_loss_sibling_positive positive odd bit exponentLarge)
    left
    exact highReturn_v_ge7_common_side_child positive bit longRange

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

/-- Full local Section 35 boundary for `v≥6`.  A retained WIN tree at the
returned contracting side and its selected Section 34 WIN child make the
common side an explicit lower WIN occurrence; the exact DRAW obligation then
ends at that same occurrence.  This theorem deliberately keeps those actual
outcome carriers as hypotheses rather than manufacturing a fresh one. -/
theorem highReturn_long_draw_to_lower_winning_boundary
    {coefficient exponent tailBit height : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) (exponentLarge : 6 ≤ exponent)
    (sideTree :
      WinningTree (B (Q coefficient (exponent - 1) tailBit)) height)
    (selectedWinning : Winning (A (B (Q coefficient (exponent - 1) tailBit))))
    (obligation :
      DrawObligation (B (Q coefficient (exponent - 1) tailBit))
        (1 - tailBit)) :
    ∃ drawLift commonHeight,
      Draw drawLift ∧
      B drawLift = B (A (B (Q coefficient (exponent - 1) tailBit))) ∧
      WinningTree (B (A (B (Q coefficient (exponent - 1) tailBit))))
        commonHeight ∧ commonHeight + 2 ≤ height := by
  obtain ⟨commonHeight, commonTree, lower⟩ :=
    highReturn_long_common_side_height_drop positive odd bit exponentLarge
      sideTree selectedWinning
  have commonWinning :
      Winning (B (A (B (Q coefficient (exponent - 1) tailBit)))) :=
    ⟨commonHeight, commonTree⟩
  obtain ⟨drawLift, drawLiftDraw, drawLiftChild, _⟩ :=
    highReturn_long_draw_to_winning_boundary positive bit exponentLarge
      obligation commonWinning
  exact ⟨drawLift, commonHeight, drawLiftDraw, drawLiftChild,
    commonTree, lower⟩

end ThreeNPlusMinusOne
