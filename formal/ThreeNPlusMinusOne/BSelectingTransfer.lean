import ThreeNPlusMinusOne.SelectingLift

set_option autoImplicit false

/-!
# Transfer of every B-selecting fork (Section 25)
-/

namespace ThreeNPlusMinusOne

/-- The exact arithmetic frame used by the universal B-selecting transfer. -/
def BSelectingTransferFrame (source : Nat) : Prop :=
  let phase := 1 - sourceASelectingBit source
  let lower := Q (embeddedValue source) 1 phase
  let upper := Q (embeddedValue source) 2 phase
  let deep := A lower
  let side := B lower
  let upperExpanding := A upper
  StateHasSource deep (B source) ∧
    StateHasSource side (B source) ∧
    ∃ common other,
      (common = A deep ∨ common = B deep) ∧
      ((A side = common ∧ B side = other) ∨
        (A side = other ∧ B side = common)) ∧
      B upperExpanding = other

/-- Section 25's large diamond is universal: no residue assumption and no
outcome assumption is needed. -/
theorem bSelecting_transferFrame (source : Nat) :
    BSelectingTransferFrame source := by
  let phase := 1 - sourceASelectingBit source
  let lower := Q (embeddedValue source) 1 phase
  let upper := Q (embeddedValue source) 2 phase
  let deep := A lower
  let side := B lower
  let upperExpanding := A upper
  obtain ⟨exponent, exponentLarge, tail⟩ :=
    sourceLift_nonselected_constantTail source
  have selectingBit := sourceASelectingBit_is_bit source
  have phaseBit : Bit phase := by
    dsimp [phase]
    rcases selectingBit with selectingZero | selectingOne
    · right
      omega
    · left
      omega
  have complement : 1 - phase = sourceASelectingBit source := by
    dsimp [phase]
    rcases selectingBit with selectingZero | selectingOne <;> omega
  have deepEquation :
      deep = Q (embeddedValue (B source)) exponent (1 - phase) := by
    simpa [deep, lower, phase, complement] using tail.equation
  have sideEquation :
      side = Q (embeddedValue (B source)) (exponent - 1)
        (1 - phase) := by
    dsimp [side]
    unfold B
    rw [show A lower = deep by rfl, deepEquation]
    exact R_Q tail.positive
      (by simpa [complement] using sourceASelectingBit_is_bit source)
      exponentLarge
  have upperEquation :
      upperExpanding = Q (3 * embeddedValue source) 1 phase := by
    dsimp [upperExpanding, upper]
    simpa using A_Q (embeddedValue_positive source) phaseBit
      (by omega : 1 ≤ 2)
  have valuation :
      3 * embeddedValue source + 1 - 2 * phase =
        2 ^ exponent * embeddedValue (B source) := by
    have expanded : deep = Q (3 * embeddedValue source) 0 phase := by
      dsimp [deep, lower]
      simpa using A_Q (embeddedValue_positive source) phaseBit
        (by omega : 1 ≤ 1)
    have equality := expanded.symm.trans deepEquation
    have productPositive :
        0 < 2 ^ exponent * embeddedValue (B source) :=
      Nat.mul_pos (Nat.pow_pos (by omega)) (embeddedValue_positive (B source))
    rcases selectingBit with selectingZero | selectingOne
    · dsimp [phase] at equality ⊢
      rw [selectingZero] at equality ⊢
      simp [Q, Nat.mul_comm] at equality ⊢
      omega
    · dsimp [phase] at equality ⊢
      rw [selectingOne] at equality ⊢
      simp [Q, Nat.mul_comm] at equality ⊢
      omega
  have adjacent := largeDiamond_adjacent_children
    (embeddedValue_positive (B source)) (embeddedValue_odd (B source))
    phaseBit exponentLarge
  have otherIdentity := largeDiamond_identity
    (embeddedValue_positive source) (embeddedValue_positive (B source))
    (embeddedValue_odd (B source)) phaseBit exponentLarge valuation
  change StateHasSource deep (B source) ∧
    StateHasSource side (B source) ∧
    ∃ common other,
      (common = A deep ∨ common = B deep) ∧
      ((A side = common ∧ B side = other) ∨
        (A side = other ∧ B side = common)) ∧
      B upperExpanding = other
  refine ⟨?_, ?_, B deep, largeDiamondOtherChild
    (embeddedValue (B source)) exponent phase, ?_, ?_, ?_⟩
  · simpa [deep, lower, phase] using
      sourceLift_nonselected_hasSource source
  · simpa [side, lower, phase] using
      sourceLift_nonselected_side_hasSource source
  · exact Or.inr rfl
  · rw [sideEquation, deepEquation]
    exact adjacent
  · rw [upperEquation]
    exact otherIdentity

/-- Pure outcome core of the Section 25 transfer. The first entry is a DRAW
at the lower lift. The second is a DRAW parent whose two children are the
upper and lower lifts, in either order. -/
theorem bSelecting_outcome_transfer
    {lower upper deep side upperExpanding common other parent : Nat}
    (lowerChildren : A lower = deep ∧ B lower = side)
    (upperChildren : A upper = upperExpanding ∧ B upper = side)
    (deepPositive : 0 < deep)
    (commonChild : common = A deep ∨ common = B deep)
    (sideChildren :
      (A side = common ∧ B side = other) ∨
        (A side = other ∧ B side = common))
    (otherIdentity : B upperExpanding = other)
    (entry :
      Draw lower ∨
        (Draw parent ∧
          ((A parent = upper ∧ B parent = lower) ∨
            (A parent = lower ∧ B parent = upper)))) :
    Draw deep ∨ Draw side := by
  have fromLower (lowerDraw : Draw lower) : Draw deep ∨ Draw side := by
    obtain ⟨next, move, nextDraw⟩ := lowerDraw.has_draw_child
    rcases move.2 with nextA | nextB
    · subst next
      rw [lowerChildren.1] at nextDraw
      exact Or.inl nextDraw
    · subst next
      rw [lowerChildren.2] at nextDraw
      exact Or.inr nextDraw
  rcases entry with lowerDraw | parentEntry
  · exact fromLower lowerDraw
  · rcases parentEntry with ⟨parentDraw, parentChildren⟩
    have lowerNotLosing : ¬ Losing lower := by
      rcases parentChildren with order | order
      · rw [← order.2]
        exact parentDraw.children_not_losing.2
      · rw [← order.1]
        exact parentDraw.children_not_losing.1
    have upperNotLosing : ¬ Losing upper := by
      rcases parentChildren with order | order
      · rw [← order.1]
        exact parentDraw.children_not_losing.1
      · rw [← order.2]
        exact parentDraw.children_not_losing.2
    by_cases lowerDraw : Draw lower
    · exact fromLower lowerDraw
    · have lowerWinning :=
        winning_of_not_draw_and_not_losing lowerDraw lowerNotLosing
      have upperDraw : Draw upper := by
        classical
        by_cases upperIsDraw : Draw upper
        · exact upperIsDraw
        · have upperWinning :=
            winning_of_not_draw_and_not_losing upperIsDraw upperNotLosing
          apply False.elim
          apply parentDraw.children_not_both_winning
          rcases parentChildren with order | order
          · rw [order.1, order.2]
            exact ⟨upperWinning, lowerWinning⟩
          · rw [order.1, order.2]
            exact ⟨lowerWinning, upperWinning⟩
      have sideNotLosing : ¬ Losing side := by
        rw [← upperChildren.2]
        exact upperDraw.children_not_losing.2
      classical
      by_cases sideDraw : Draw side
      · exact Or.inr sideDraw
      · have sideWinning :=
          winning_of_not_draw_and_not_losing sideDraw sideNotLosing
        have deepLosing : Losing deep := by
          rw [← lowerChildren.1]
          apply lowerWinning.A_losing_of_B_not_losing
          rw [lowerChildren.2]
          exact sideNotLosing
        have upperExpandingDraw : Draw upperExpanding := by
          rw [← upperChildren.1]
          apply upperDraw.A_of_B_winning
          rw [upperChildren.2]
          exact sideWinning
        exact False.elim (largeDiamond_outcome_contradiction
          deepPositive deepLosing sideWinning upperExpandingDraw
          commonChild sideChildren (Or.inr otherIdentity.symm))

/-- Complete universal transfer rule boxed in Section 25. -/
theorem bSelecting_draw_transfer
    {source parent : Nat}
    (entry :
      Draw (Q (embeddedValue source) 1
        (1 - sourceASelectingBit source)) ∨
      (Draw parent ∧
        ((A parent = Q (embeddedValue source) 2
            (1 - sourceASelectingBit source) ∧
          B parent = Q (embeddedValue source) 1
            (1 - sourceASelectingBit source)) ∨
         (A parent = Q (embeddedValue source) 1
            (1 - sourceASelectingBit source) ∧
          B parent = Q (embeddedValue source) 2
            (1 - sourceASelectingBit source))))) :
    Draw (A (Q (embeddedValue source) 1
      (1 - sourceASelectingBit source))) ∨
    Draw (B (Q (embeddedValue source) 1
      (1 - sourceASelectingBit source))) := by
  have frame := bSelecting_transferFrame source
  dsimp [BSelectingTransferFrame] at frame
  rcases frame.2.2 with
    ⟨common, other, commonChild, sideChildren, otherIdentity⟩
  have phaseBit : Bit (1 - sourceASelectingBit source) := by
    have phaseData := sourceASelectingBit_is_bit source
    rcases phaseData with phaseZero | phaseOne
    · exact Or.inr (by omega)
    · exact Or.inl (by omega)
  have lowerPositive :
      0 < Q (embeddedValue source) 1
        (1 - sourceASelectingBit source) := by
    have coefficientPositive := embeddedValue_positive source
    rcases phaseBit with phaseZero | phaseOne <;> simp [Q] <;> omega
  apply bSelecting_outcome_transfer
    (common := common) (other := other)
    (lowerChildren := ⟨rfl, rfl⟩)
    (upperChildren := ⟨rfl, ?_⟩)
    (deepPositive := A_pos lowerPositive)
    (commonChild := commonChild)
    (sideChildren := sideChildren)
    (otherIdentity := otherIdentity)
    entry
  exact (B_Q_one_eq_two (embeddedValue_positive source)
    (embeddedValue_odd source) phaseBit).symm

end ThreeNPlusMinusOne
