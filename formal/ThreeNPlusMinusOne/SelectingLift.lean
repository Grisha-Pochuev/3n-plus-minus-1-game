import ThreeNPlusMinusOne.LengthTwo

set_option autoImplicit false

/-!
# The A-selecting lift diamond (Section 24)
-/

namespace ThreeNPlusMinusOne

/-- The side child of every A-selecting source lift is an ordinary child of
the selected source `A(source)`. -/
theorem selectedLift_side_child (source : Nat) :
    B (Q (embeddedValue source) 1 (sourceASelectingBit source)) =
        A (A source) ∨
      B (Q (embeddedValue source) 1 (sourceASelectingBit source)) =
        B (A source) := by
  let phase := sourceASelectingBit source
  have phaseData : Bit phase := by
    simpa [phase] using sourceASelectingBit_is_bit source
  have selectedData := sourceASelectingBit_is_bit (A source)
  have liftEquation := A_sourceLift_selected source
  unfold B
  rw [liftEquation]
  by_cases selected : 1 - phase = sourceASelectingBit (A source)
  · left
    rw [selected]
    exact R_sourceLift_selected (A source)
  · have opposite :
        1 - phase = 1 - sourceASelectingBit (A source) := by
      rcases phaseData with phaseZero | phaseOne <;>
        rcases selectedData with selectedZero | selectedOne <;> omega
    right
    rw [opposite]
    exact R_sourceLift_nonselected (A source)

theorem selectedLift_side_eq_A
    {source : Nat}
    (parity : A (A source) % 2 = sourceASelectingBit source) :
    B (Q (embeddedValue source) 1 (sourceASelectingBit source)) =
      A (A source) := by
  have nextParity := A_parity (A source)
  have nextSelecting :
      sourceASelectingBit (A source) = 1 - A (A source) % 2 := by
    unfold sourceASelectingBit
    rw [← nextParity]
  have phaseData := sourceASelectingBit_is_bit source
  have parityData : Bit (A (A source) % 2) := by
    unfold Bit
    omega
  have selected :
      1 - sourceASelectingBit source =
        sourceASelectingBit (A source) := by
    rw [nextSelecting]
    rcases phaseData with phaseZero | phaseOne <;>
      rcases parityData with parityZero | parityOne <;> omega
  unfold B
  rw [A_sourceLift_selected source, selected]
  exact R_sourceLift_selected (A source)

theorem selectedLift_side_eq_B
    {source : Nat}
    (parity : A (A source) % 2 ≠ sourceASelectingBit source) :
    B (Q (embeddedValue source) 1 (sourceASelectingBit source)) =
      B (A source) := by
  have nextParity := A_parity (A source)
  have nextSelecting :
      sourceASelectingBit (A source) = 1 - A (A source) % 2 := by
    unfold sourceASelectingBit
    rw [← nextParity]
  have phaseData := sourceASelectingBit_is_bit source
  have parityData : Bit (A (A source) % 2) := by
    unfold Bit
    omega
  have opposite :
      1 - sourceASelectingBit source =
        1 - sourceASelectingBit (A source) := by
    rw [nextSelecting]
    rcases phaseData with phaseZero | phaseOne <;>
      rcases parityData with parityZero | parityOne <;> omega
  unfold B
  rw [A_sourceLift_selected source, opposite]
  exact R_sourceLift_nonselected (A source)

/-- If `A(source)` is the forced losing child of a winning source, the side
of the selected lift has a concrete winning proof tree at least two levels
lower than every supplied winning proof tree of `source`. -/
theorem selectedLift_side_heightDrop
    {source height : Nat} (tree : WinningTree source height)
    (selectedLosing : Losing (A source))
    (otherWinning : Winning (B source)) :
    let side :=
      B (Q (embeddedValue source) 1 (sourceASelectingBit source))
    ∃ sideHeight,
      WinningTree side sideHeight ∧ sideHeight + 2 ≤ height := by
  dsimp only
  let side := B (Q (embeddedValue source) 1
    (sourceASelectingBit source))
  have sourcePositive : 0 < source := by
    cases tree with
    | moveA nonterminal reply => exact nonterminal
    | moveB nonterminal reply => exact nonterminal
  have sideChild : side = A (A source) ∨ side = B (A source) := by
    simpa [side] using selectedLift_side_child source
  have selectedChildren := selectedLosing.children_winning (A_pos sourcePositive)
  have sideWinning : Winning side := by
    rcases sideChild with sideA | sideB
    · rw [sideA]
      exact selectedChildren.1
    · rw [sideB]
      exact selectedChildren.2
  have sidePositive : 0 < side := by
    by_cases sideZero : side = 0
    · apply False.elim
      apply sideWinning.not_losing
      rw [sideZero]
      exact Losing.terminal
    · omega
  cases tree with
  | moveA nonterminal reply =>
      obtain ⟨sideHeight, sideTree, lower⟩ :=
        reply.positive_child_lower sidePositive sideChild
      exact ⟨sideHeight, sideTree, by omega⟩
  | moveB nonterminal reply =>
      exact False.elim (otherWinning.not_losing ⟨_, reply⟩)

end ThreeNPlusMinusOne
