import ThreeNPlusMinusOne.HighValuationReturn

set_option autoImplicit false

/-!
# The retained height drop in the high-valuation return (Section 34)

Section 33 returns to a constant-tail lift.  The arithmetic below isolates the
following local fact used in Section 34: if its contracting child and the
returned side are finite WIN states, then the next common child is represented
by an actual lower `WinningTree` occurrence.  This is a local occurrence
payment only; it does not claim that a later DRAW continuation reaches that
occurrence.
-/

namespace ThreeNPlusMinusOne

/-- The contracting child of the Section 33 returned constant-tail state is
the stated lower side `Z`. -/
theorem highReturn_contracting_child
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 4 ≤ exponent) :
    B (Q coefficient (exponent - 1) tailBit) =
      Q (3 * coefficient) (exponent - 3) tailBit := by
  simpa [show exponent - 1 - 2 = exponent - 3 by omega] using
    B_Q positive bit (by omega : 3 ≤ exponent - 1)

/-- The expanding child of the same returned state is the retained LOSS
witness `L` of Section 34. -/
theorem highReturn_expanding_child
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 4 ≤ exponent) :
    A (Q coefficient (exponent - 1) tailBit) =
      Q (3 * coefficient) (exponent - 2) tailBit := by
  simpa [show exponent - 1 - 1 = exponent - 2 by omega] using
    A_Q positive bit (by omega : 1 ≤ exponent - 1)

/-- At the boundary exponent `4`, the two Section 34 states are the
exponent-two/one pair and hence have the same contracting child. -/
theorem highReturn_common_child_boundary
    {coefficient tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) :
    B (Q (3 * coefficient) 2 tailBit) =
      B (Q (3 * coefficient) 1 tailBit) := by
  have triplePositive : 0 < 3 * coefficient := by omega
  have tripleOdd : OddNat (3 * coefficient) := by
    obtain ⟨half, shape⟩ := odd
    exact ⟨3 * half + 1, by omega⟩
  exact (B_Q_one_eq_two triplePositive tripleOdd bit).symm

/-- At every exponent at least `5`, the two Section 34 states have the
explicit common child prescribed by the long-tail recurrences. -/
theorem highReturn_common_child_long
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 5 ≤ exponent) :
    B (Q (3 * coefficient) (exponent - 2) tailBit) =
        Q (9 * coefficient) (exponent - 4) tailBit ∧
      A (Q (3 * coefficient) (exponent - 3) tailBit) =
        Q (9 * coefficient) (exponent - 4) tailBit := by
  have triplePositive : 0 < 3 * coefficient := by omega
  constructor
  · simpa [show 3 * (3 * coefficient) = 9 * coefficient by omega,
      show exponent - 2 - 2 = exponent - 4 by omega] using
      B_Q triplePositive bit (by omega : 3 ≤ exponent - 2)
  · simpa [show 3 * (3 * coefficient) = 9 * coefficient by omega,
      show exponent - 3 - 1 = exponent - 4 by omega] using
      A_Q triplePositive bit (by omega : 1 ≤ exponent - 3)

/-- At the boundary valuation `v=4`, the expanding and contracting children
of `C=Q_3^e(c)` have the same next child. -/
theorem highReturn_boundary_common_grandchild
    {coefficient tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) :
    B (A (Q coefficient 3 tailBit)) =
      B (B (Q coefficient 3 tailBit)) := by
  calc
    B (A (Q coefficient 3 tailBit)) = B (Q (3 * coefficient) 2 tailBit) := by
      rw [A_Q positive bit (by omega : 1 ≤ 3)]
    _ = B (Q (3 * coefficient) 1 tailBit) :=
      highReturn_common_child_boundary positive odd bit
    _ = B (B (Q coefficient 3 tailBit)) := by
      rw [B_Q positive bit (by omega : 3 ≤ 3)]

/-- Above the boundary valuation, the Section 34 two-edge paths from `C`
meet at the explicit constant-tail coordinate `Q_{v-4}^e(9c)`. -/
theorem highReturn_long_common_grandchild
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 5 ≤ exponent) :
    B (A (Q coefficient (exponent - 1) tailBit)) =
      A (B (Q coefficient (exponent - 1) tailBit)) := by
  have common := highReturn_common_child_long positive bit exponentLarge
  calc
    B (A (Q coefficient (exponent - 1) tailBit)) =
        B (Q (3 * coefficient) (exponent - 2) tailBit) := by
      rw [highReturn_expanding_child positive bit (by omega)]
    _ = Q (9 * coefficient) (exponent - 4) tailBit := common.1
    _ = A (Q (3 * coefficient) (exponent - 3) tailBit) := common.2.symm
    _ = A (B (Q coefficient (exponent - 1) tailBit)) := by
      rw [highReturn_contracting_child positive bit (by omega)]

/-- A `WIN` tree whose `B` child is already known to be `WIN` must select its
`A` child.  Any `B` child of that selected LOSS reply is therefore a concrete
WIN occurrence at least two proof levels lower. -/
theorem WinningTree.twoLevelDrop_of_B_winning
    {state common height : Nat}
    (tree : WinningTree state height) (siblingWinning : Winning (B state))
    (commonEquation : common = B (A state)) :
    ∃ commonHeight, WinningTree common commonHeight ∧
      commonHeight + 2 ≤ height := by
  cases tree with
  | moveA nonterminal reply =>
      have replyOutcome : Losing (A state) := ⟨_, reply⟩
      have commonWinning : Winning common := by
        rw [commonEquation]
        exact (replyOutcome.children_winning (A_pos nonterminal)).2
      have commonPositive : 0 < common := by
        by_cases commonZero : common = 0
        · apply False.elim
          apply commonWinning.not_losing
          rw [commonZero]
          exact terminal_losing
        · omega
      obtain ⟨commonHeight, commonTree, lower⟩ :=
        reply.positive_child_lower commonPositive (Or.inr commonEquation)
      exact ⟨commonHeight, commonTree, by omega⟩
  | moveB _ reply =>
      apply False.elim
      exact siblingWinning.not_losing ⟨_, reply⟩

/-- Section 34's strict local height payment.  Once the returned state `C`
has a concrete WIN tree and its side `Z` is WIN, the child `W=B(A(C))` is a
concrete WIN occurrence at least two levels below the given `C` occurrence. -/
theorem highReturn_common_child_height_drop
    {coefficient exponent tailBit height : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 4 ≤ exponent)
    (tree : WinningTree (Q coefficient (exponent - 1) tailBit) height)
    (sideWinning : Winning (Q (3 * coefficient) (exponent - 3) tailBit)) :
    ∃ commonHeight,
      WinningTree (B (Q (3 * coefficient) (exponent - 2) tailBit))
        commonHeight ∧
        commonHeight + 2 ≤ height := by
  apply WinningTree.twoLevelDrop_of_B_winning tree
  · rw [highReturn_contracting_child positive bit exponentLarge]
    exact sideWinning
  · rw [highReturn_expanding_child positive bit exponentLarge]

/-- The boundary `v=4` instance of Section 34's height payment retains the
actual common-child coordinate. -/
theorem highReturn_boundary_height_drop
    {coefficient tailBit height : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (tree : WinningTree (Q coefficient 3 tailBit) height)
    (sideWinning : Winning (Q (3 * coefficient) 1 tailBit)) :
    ∃ commonHeight,
      WinningTree (B (Q (3 * coefficient) 2 tailBit)) commonHeight ∧
        commonHeight + 2 ≤ height := by
  simpa using highReturn_common_child_height_drop positive bit
    (by omega : 4 ≤ 4) tree sideWinning

/-- The long `v≥5` instance of Section 34's height payment names its common
child as `Q_{v-4}^e(9c)`. -/
theorem highReturn_long_height_drop
    {coefficient exponent tailBit height : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 5 ≤ exponent)
    (tree : WinningTree (Q coefficient (exponent - 1) tailBit) height)
    (sideWinning : Winning (Q (3 * coefficient) (exponent - 3) tailBit)) :
    ∃ commonHeight,
      WinningTree (Q (9 * coefficient) (exponent - 4) tailBit) commonHeight ∧
        commonHeight + 2 ≤ height := by
  obtain ⟨commonHeight, commonTree, lower⟩ :=
    highReturn_common_child_height_drop positive bit (by omega) tree sideWinning
  refine ⟨commonHeight, ?_, lower⟩
  rw [← (highReturn_common_child_long positive bit exponentLarge).1]
  exact commonTree

end ThreeNPlusMinusOne
