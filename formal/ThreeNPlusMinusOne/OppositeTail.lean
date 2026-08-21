import ThreeNPlusMinusOne.ASelectingFactor

set_option autoImplicit false

/-!
# The opposite-tail twin switch (Section 29)

The bounded factor escape of Section 28 retains a concrete losing state.
This file proves that its expanding child is exactly the opposite-tail twin
of the lower member of the factor frame.  The result is local: it records the
arithmetic identity and the forced finite outcomes, without claiming that the
global DRAW refinement has been constructed.
-/

namespace ThreeNPlusMinusOne

/-- Section 29's arithmetic identity.  If the upper child of the factor state
has the adjacent-frame form from Section 28, then the retained selected state
has the opposite-tail twin as its expanding child. -/
theorem selectedFactor_oppositeTwin
    {source lowerExponent : Nat}
    (expandingFrame :
      A (A (Q (embeddedValue source) 2
        (sourceASelectingBit source))) =
        Q (embeddedValue (B (Q (embeddedValue source) 1
          (sourceASelectingBit source)))) (lowerExponent + 1)
          (1 - sourceASelectingBit source)) :
    A (A (Q (embeddedValue source) 1
      (sourceASelectingBit source))) =
      Q (embeddedValue (B (Q (embeddedValue source) 1
        (sourceASelectingBit source)))) lowerExponent
        (sourceASelectingBit source) := by
  have phaseData := sourceASelectingBit_is_bit source
  rcases phaseData with phaseZero | phaseOne
  · rw [phaseZero] at expandingFrame ⊢
    simp [Q, A, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] at expandingFrame ⊢
    omega
  · rw [phaseOne] at expandingFrame ⊢
    simp [Q, A, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] at expandingFrame ⊢
    have sourcePositive := embeddedValue_positive source
    have sidePositive := embeddedValue_positive
      (B (Q (embeddedValue source) 1 1))
    omega

/-- The full local Section 29 switch exported by a bounded Section 28 factor
escape.  Besides the exact frame and exponent bound, it records that the
opposite-tail twin is WIN (as a child of the retained LOSS state) and that
the lower factor-frame member is non-losing (as a child of a DRAW state). -/
theorem ASelectingFactorEscape.oppositeTailSwitch
    {source : Nat} (escape : ASelectingFactorEscape source) :
    let phase := sourceASelectingBit source
    let lower := Q (embeddedValue source) 1 phase
    let upper := Q (embeddedValue source) 2 phase
    let side := B lower
    let selected := A lower
    let factor := A upper
    ∃ lowerExponent,
      1 ≤ lowerExponent ∧ lowerExponent ≤ 3 ∧
        Losing selected ∧
        Winning (Q (embeddedValue side) lowerExponent phase) ∧
        ¬ Losing (Q (embeddedValue side) lowerExponent (1 - phase)) ∧
        Draw factor ∧
        A factor = Q (embeddedValue side) (lowerExponent + 1)
          (1 - phase) ∧
        B factor = Q (embeddedValue side) lowerExponent
          (1 - phase) ∧
        A selected = Q (embeddedValue side) lowerExponent phase := by
  dsimp [ASelectingFactorEscape] at escape ⊢
  obtain ⟨lowerExponent, exponentPositive, exponentBound,
    _lowerWinning, _upperDraw, _sideWinning, selectedLosing, factorDraw,
    expandingFrame, contractingFrame⟩ := escape
  let selected := A (Q (embeddedValue source) 1
    (sourceASelectingBit source))
  have lowerPositive :
      0 < Q (embeddedValue source) 1 (sourceASelectingBit source) := by
    have sourceValuePositive := embeddedValue_positive source
    have phaseData := sourceASelectingBit_is_bit source
    rcases phaseData with phaseZero | phaseOne
    · rw [phaseZero]
      simp [Q]
      omega
    · rw [phaseOne]
      simp [Q]
      omega
  have selectedPositive : 0 < selected := by
    dsimp [selected]
    exact A_pos lowerPositive
  have selectedChildren := selectedLosing.children_winning selectedPositive
  have twinEquation := selectedFactor_oppositeTwin expandingFrame
  have twinWinning :
      Winning (Q (embeddedValue
        (B (Q (embeddedValue source) 1 (sourceASelectingBit source))))
        lowerExponent (sourceASelectingBit source)) := by
    rw [← twinEquation]
    exact selectedChildren.1
  have lowerFrameNotLosing :
      ¬ Losing (Q (embeddedValue
        (B (Q (embeddedValue source) 1 (sourceASelectingBit source))))
        lowerExponent (1 - sourceASelectingBit source)) := by
    rw [← contractingFrame]
    exact factorDraw.children_not_losing.2
  exact ⟨lowerExponent, exponentPositive, exponentBound, selectedLosing,
    twinWinning, lowerFrameNotLosing, factorDraw, expandingFrame,
    contractingFrame, twinEquation⟩

end ThreeNPlusMinusOne
