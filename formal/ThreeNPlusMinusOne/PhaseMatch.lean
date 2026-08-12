import ThreeNPlusMinusOne.LargeDiamond

set_option autoImplicit false

/-!
# Phase-match adjacent source pair (Section 21)
-/

namespace ThreeNPlusMinusOne

/--
The second selected lift in every nondecreasing phase-match row has the
exact adjacent pair used at the start of Section 21.  Keeping this as a
named frame avoids replacing the unbounded suffix operation by a residue
lookup later in the outcome argument.
-/
def PhaseMatchAdjacentFrame (source : Nat) : Prop :=
  let tailBit := sourceASelectingBit source
  let returnedSource := B (A source)
  let parent := Q (embeddedValue (A source)) 1 (1 - tailBit)
  sourceASelectingBit returnedSource = tailBit ∧
    B parent = Q (embeddedValue returnedSource) 1 tailBit ∧
      A parent = Q (embeddedValue returnedSource) 2 tailBit

private theorem phaseMatchAdjacentFrame_of_expanding
    {source : Nat}
    (phase :
      sourceASelectingBit (B (A source)) =
        sourceASelectingBit source)
    (expanding :
      A (Q (embeddedValue (A source)) 1
          (1 - sourceASelectingBit source)) =
        Q (embeddedValue (B (A source))) 2
          (sourceASelectingBit source)) :
    PhaseMatchAdjacentFrame source := by
  dsimp [PhaseMatchAdjacentFrame]
  refine ⟨phase, ?_, expanding⟩
  unfold B
  rw [expanding]
  exact R_Q (embeddedValue_positive (B (A source)))
    (sourceASelectingBit_is_bit source) (by omega)

theorem phaseMatchAdjacentFrame_zero (t : Nat) :
    PhaseMatchAdjacentFrame (32 * t) := by
  apply phaseMatchAdjacentFrame_of_expanding
  · exact returnPhase_match_zero t
  · rw [show 32 * t = 16 * (2 * t) by omega, returnRow_zero]
    simp [A, Q, embeddedValue_formula, sourceASelectingBit]
    omega

theorem phaseMatchAdjacentFrame_ten (t : Nat) :
    PhaseMatchAdjacentFrame (32 * t + 10) := by
  apply phaseMatchAdjacentFrame_of_expanding
  · exact returnPhase_match_ten t
  · rw [show 32 * t + 10 = 16 * (2 * t) + 10 by omega,
      returnRow_ten]
    simp [A, Q, embeddedValue_formula, sourceASelectingBit]
    omega

theorem phaseMatchAdjacentFrame_twenty_one (t : Nat) :
    PhaseMatchAdjacentFrame (32 * t + 21) := by
  apply phaseMatchAdjacentFrame_of_expanding
  · exact returnPhase_match_twenty_one t
  · rw [show 32 * t + 21 = 16 * (2 * t + 1) + 5 by omega,
      returnRow_five]
    simp [A, Q, embeddedValue_formula, sourceASelectingBit]
    omega

theorem phaseMatchAdjacentFrame_thirty_one (t : Nat) :
    PhaseMatchAdjacentFrame (32 * t + 31) := by
  apply phaseMatchAdjacentFrame_of_expanding
  · exact returnPhase_match_thirty_one t
  · rw [show 32 * t + 31 = 16 * (2 * t + 1) + 15 by omega,
      returnRow_fifteen]
    simp [A, Q, embeddedValue_formula, sourceASelectingBit]
    omega

/--
The first inequality of Section 21 in coordinate-free form.  If `z` is the
ordinary returned source and `rho` is the canonical source of the common
boundary child, the affine return bound forces `rho < source`.  No residue
class is used to decode `R` here.
-/
theorem phaseMatch_commonChild_source_strict
    {source z rho : Nat}
    (sourceLarge : 4 ≤ source)
    (returnBound : 8 * z ≤ 9 * source + 3)
    (coordinates :
      StateHasSource
        (B (Q (embeddedValue z) 1 (sourceASelectingBit z))) rho) :
    rho < source := by
  obtain ⟨sourceExponent, tailExponent, tailBit, coefficient,
    tail, sourceData⟩ := coordinates
  have childEquation :
      B (Q (embeddedValue z) 1 (sourceASelectingBit z)) =
        boundaryChild (embeddedValue z) (sourceASelectingBit z) :=
    B_Q_one_eq_boundaryChild (embeddedValue_positive z)
      (sourceASelectingBit_is_bit z)
  have coefficientBound := boundaryChild_coefficient_bound
    (embeddedValue_odd z) (sourceASelectingBit_is_bit z)
    childEquation tail
  have scaledCoefficientBound :
      4 * coefficient ≤ 3 * embeddedValue z + 1 := by
    omega
  have embeddedBound := sourceData.embedded_le_coefficient
  rw [embeddedValue_formula] at scaledCoefficientBound embeddedBound
  omega

theorem phaseMatch_return_bound_zero (t : Nat) :
    8 * B (A (32 * t)) ≤ 9 * (32 * t) + 3 := by
  rw [show 32 * t = 16 * (2 * t) by omega, returnRow_zero]
  omega

theorem phaseMatch_return_bound_ten (t : Nat) :
    8 * B (A (32 * t + 10)) ≤ 9 * (32 * t + 10) + 3 := by
  rw [show 32 * t + 10 = 16 * (2 * t) + 10 by omega,
    returnRow_ten]
  omega

theorem phaseMatch_return_bound_twenty_one (t : Nat) :
    8 * B (A (32 * t + 21)) ≤ 9 * (32 * t + 21) + 3 := by
  rw [show 32 * t + 21 = 16 * (2 * t + 1) + 5 by omega,
    returnRow_five]
  omega

theorem phaseMatch_return_bound_thirty_one (t : Nat) :
    8 * B (A (32 * t + 31)) ≤ 9 * (32 * t + 31) + 3 := by
  rw [show 32 * t + 31 = 16 * (2 * t + 1) + 15 by omega,
    returnRow_fifteen]
  omega

theorem phaseMatch_commonChild_source_strict_zero
    {t rho : Nat} (tPositive : 0 < t)
    (coordinates :
      StateHasSource
        (B (Q (embeddedValue (B (A (32 * t)))) 1
          (sourceASelectingBit (32 * t)))) rho) :
    rho < 32 * t := by
  have phase := returnPhase_match_zero t
  rw [← phase] at coordinates
  exact phaseMatch_commonChild_source_strict (by omega)
    (phaseMatch_return_bound_zero t) coordinates

theorem phaseMatch_commonChild_source_strict_ten
    {t rho : Nat}
    (coordinates :
      StateHasSource
        (B (Q (embeddedValue (B (A (32 * t + 10)))) 1
          (sourceASelectingBit (32 * t + 10)))) rho) :
    rho < 32 * t + 10 := by
  have phase := returnPhase_match_ten t
  rw [← phase] at coordinates
  exact phaseMatch_commonChild_source_strict (by omega)
    (phaseMatch_return_bound_ten t) coordinates

theorem phaseMatch_commonChild_source_strict_twenty_one
    {t rho : Nat}
    (coordinates :
      StateHasSource
        (B (Q (embeddedValue (B (A (32 * t + 21)))) 1
          (sourceASelectingBit (32 * t + 21)))) rho) :
    rho < 32 * t + 21 := by
  have phase := returnPhase_match_twenty_one t
  rw [← phase] at coordinates
  exact phaseMatch_commonChild_source_strict (by omega)
    (phaseMatch_return_bound_twenty_one t) coordinates

theorem phaseMatch_commonChild_source_strict_thirty_one
    {t rho : Nat}
    (coordinates :
      StateHasSource
        (B (Q (embeddedValue (B (A (32 * t + 31)))) 1
          (sourceASelectingBit (32 * t + 31)))) rho) :
    rho < 32 * t + 31 := by
  have phase := returnPhase_match_thirty_one t
  rw [← phase] at coordinates
  exact phaseMatch_commonChild_source_strict (by omega)
    (phaseMatch_return_bound_thirty_one t) coordinates

private theorem R_long_twenty_one (t : Nat) :
    R (1296 * t + 218) < 128 * t + 21 := by
  calc
    R (1296 * t + 218) = R (648 * t + 109) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (324 * t + 54) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (162 * t + 27) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ ≤ (162 * t + 27) / 2 := R_le_half _
    _ < 128 * t + 21 := by omega

private theorem R_long_sixty_three (t : Nat) :
    R (1296 * t + 645) < 128 * t + 63 := by
  calc
    R (1296 * t + 645) = R (648 * t + 322) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (324 * t + 161) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (162 * t + 80) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ ≤ (162 * t + 80) / 2 := R_le_half _
    _ < 128 * t + 63 := by omega

private theorem R_long_sixty_four (t : Nat) :
    R (1296 * t + 650) < 128 * t + 64 := by
  calc
    R (1296 * t + 650) = R (648 * t + 325) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (324 * t + 162) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (162 * t + 81) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ ≤ (162 * t + 81) / 2 := R_le_half _
    _ < 128 * t + 64 := by omega

private theorem R_long_one_hundred_six (t : Nat) :
    R (1296 * t + 1077) < 128 * t + 106 := by
  calc
    R (1296 * t + 1077) = R (648 * t + 538) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (324 * t + 269) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ = R (162 * t + 134) := by
      rw [R_of_alternates (by omega) (by omega)]
      congr 1
      omega
    _ ≤ (162 * t + 134) / 2 := R_le_half _
    _ < 128 * t + 106 := by omega

private theorem removeTwos_exponent_at_least_four
    {raw coefficient exponent quotient : Nat}
    (coefficientOdd : OddNat coefficient)
    (equation : raw = 2 ^ exponent * coefficient)
    (divisible : raw = 16 * quotient) :
    4 ≤ exponent := by
  by_cases large : 4 ≤ exponent
  · exact large
  · have small :
        exponent = 0 ∨ exponent = 1 ∨ exponent = 2 ∨ exponent = 3 := by
      omega
    obtain ⟨half, coefficientShape⟩ := coefficientOdd
    rcases small with rfl | rfl | rfl | rfl <;>
      simp at equation <;> omega

/--
If the alternating raw core of `d` contains at least four factors of two,
both children of `d` have canonical coefficient source `R d`.  This is the
unbounded version of the long-suffix identity used in the second case of
Section 21.
-/
theorem longAlternating_children_have_source
    {d : Nat} (divisible : ∃ quotient, alternatingCore d = 16 * quotient) :
    StateHasSource (A d) (R d) ∧ StateHasSource (B d) (R d) := by
  obtain ⟨quotient, divisibleEquation⟩ := divisible
  obtain ⟨coefficientOdd, exponent, coreEquation⟩ :=
    alternatingCore_removeTwos d
  have coefficientEquation : 2 * A (R d) + 1 = embeddedValue (R d) := by
    rfl
  rw [coefficientEquation] at coreEquation coefficientOdd
  have exponentLarge := removeTwos_exponent_at_least_four
    coefficientOdd coreEquation divisibleEquation
  let tailBit := 1 - d % 2
  have dBit : Bit (d % 2) := by
    unfold Bit
    omega
  have tailBitData : Bit tailBit := by
    dsimp [tailBit]
    rcases dBit with hzero | hone
    · right
      omega
    · left
      omega
  have powStep : 2 ^ exponent = 2 * 2 ^ (exponent - 1) := by
    obtain ⟨rest, exponentShape⟩ : ∃ rest, exponent = rest + 1 :=
      ⟨exponent - 1, by omega⟩
    rw [exponentShape, Nat.pow_succ]
    simp [Nat.mul_comm]
  have expandingEquation :
      A d = Q (embeddedValue (R d)) (exponent - 1) tailBit := by
    rw [powStep] at coreEquation
    rcases dBit with dEven | dOdd
    · simp [alternatingCore, A, Q, tailBit, dEven,
        Nat.mul_assoc, Nat.mul_comm] at coreEquation ⊢
      omega
    · simp [alternatingCore, A, Q, tailBit, dOdd,
        Nat.mul_assoc, Nat.mul_comm] at coreEquation ⊢
      omega
  have contractingEquation :
      B d = Q (embeddedValue (R d)) (exponent - 2) tailBit := by
    unfold B
    rw [expandingEquation]
    have reduced := R_Q (embeddedValue_positive (R d)) tailBitData
      (by omega : 2 ≤ exponent - 1)
    simpa only [show exponent - 1 - 1 = exponent - 2 by omega] using reduced
  have expandingTail :
      IsConstantTail (A d) (embeddedValue (R d))
        (exponent - 1) tailBit :=
    ⟨embeddedValue_positive (R d), embeddedValue_odd (R d),
      by omega, tailBitData, expandingEquation⟩
  have contractingTail :
      IsConstantTail (B d) (embeddedValue (R d))
        (exponent - 2) tailBit :=
    ⟨embeddedValue_positive (R d), embeddedValue_odd (R d),
      by omega, tailBitData, contractingEquation⟩
  constructor
  · exact ⟨0, exponent - 1, tailBit, embeddedValue (R d),
      expandingTail, ⟨by simp⟩⟩
  · exact ⟨0, exponent - 2, tailBit, embeddedValue (R d),
      contractingTail, ⟨by simp⟩⟩

/-- The four long-suffix phase-match rows have an ordinary common child
strictly below the globally minimal source candidate. -/
theorem phaseMatch_commonChild_valueDrop_twenty_one (t : Nat) :
    B (Q (embeddedValue (B (A (128 * t + 21)))) 1
      (sourceASelectingBit (128 * t + 21))) < 128 * t + 21 := by
  have returned : B (A (128 * t + 21)) = 144 * t + 24 := by
    rw [show 128 * t + 21 = 16 * (2 * (4 * t) + 1) + 5 by omega,
      returnRow_five]
    omega
  have phase : sourceASelectingBit (128 * t + 21) = 1 := by
    unfold sourceASelectingBit
    omega
  rw [returned, phase]
  unfold B
  rw [show A (Q (embeddedValue (144 * t + 24)) 1 1) =
      1296 * t + 218 by
    simp [A, Q, embeddedValue_formula]
    omega]
  exact R_long_twenty_one t

theorem phaseMatch_commonChild_valueDrop_sixty_three (t : Nat) :
    B (Q (embeddedValue (B (A (128 * t + 63)))) 1
      (sourceASelectingBit (128 * t + 63))) < 128 * t + 63 := by
  have returned : B (A (128 * t + 63)) = 144 * t + 71 := by
    rw [show 128 * t + 63 = 16 * (2 * (4 * t + 1) + 1) + 15 by omega,
      returnRow_fifteen]
    omega
  have phase : sourceASelectingBit (128 * t + 63) = 0 := by
    unfold sourceASelectingBit
    omega
  rw [returned, phase]
  unfold B
  rw [show A (Q (embeddedValue (144 * t + 71)) 1 0) =
      1296 * t + 645 by
    simp [A, Q, embeddedValue_formula]
    omega]
  exact R_long_sixty_three t

theorem phaseMatch_commonChild_valueDrop_sixty_four (t : Nat) :
    B (Q (embeddedValue (B (A (128 * t + 64)))) 1
      (sourceASelectingBit (128 * t + 64))) < 128 * t + 64 := by
  have returned : B (A (128 * t + 64)) = 144 * t + 72 := by
    rw [show 128 * t + 64 = 16 * (2 * (4 * t + 2)) by omega,
      returnRow_zero]
    omega
  have phase : sourceASelectingBit (128 * t + 64) = 1 := by
    unfold sourceASelectingBit
    omega
  rw [returned, phase]
  unfold B
  rw [show A (Q (embeddedValue (144 * t + 72)) 1 1) =
      1296 * t + 650 by
    simp [A, Q, embeddedValue_formula]
    omega]
  exact R_long_sixty_four t

theorem phaseMatch_commonChild_valueDrop_one_hundred_six (t : Nat) :
    B (Q (embeddedValue (B (A (128 * t + 106)))) 1
      (sourceASelectingBit (128 * t + 106))) < 128 * t + 106 := by
  have returned : B (A (128 * t + 106)) = 144 * t + 119 := by
    rw [show 128 * t + 106 = 16 * (2 * (4 * t + 3)) + 10 by omega,
      returnRow_ten]
    omega
  have phase : sourceASelectingBit (128 * t + 106) = 0 := by
    unfold sourceASelectingBit
    omega
  rw [returned, phase]
  unfold B
  rw [show A (Q (embeddedValue (144 * t + 119)) 1 0) =
      1296 * t + 1077 by
    simp [A, Q, embeddedValue_formula]
    omega]
  exact R_long_one_hundred_six t

/--
The two children of the high phase-match state are adjacent constant-tail
states whose coefficient is exactly the embedded common child `J(c)`.
-/
theorem phaseMatch_high_adjacent_pair
    {z tailBit : Nat} (bit : Bit tailBit)
    (phaseMatch : tailBit = sourceASelectingBit z) :
    ∃ exponent,
      2 ≤ exponent ∧
        A (Q (3 * embeddedValue z) 1 tailBit) =
          Q (embeddedValue
              (B (Q (embeddedValue z) 1 tailBit)))
            exponent (1 - tailBit) ∧
        B (Q (3 * embeddedValue z) 1 tailBit) =
          Q (embeddedValue
              (B (Q (embeddedValue z) 1 tailBit)))
            (exponent - 1) (1 - tailBit) := by
  let a := embeddedValue z
  have aPositive : 0 < a := embeddedValue_positive z
  have aOdd : OddNat a := embeddedValue_odd z
  rcases bit with tailZero | tailOne
  · subst tailBit
    have phaseZero : sourceASelectingBit z = 0 := tailZero
    have aMod : a % 4 = 3 := by
      exact embeddedValue_mod_four_of_selectingBit_zero phaseZero
    have tripleOdd : OddNat (3 * a) := by
      obtain ⟨half, aShape⟩ := aOdd
      exact ⟨3 * half + 1, by dsimp [a] at aShape ⊢; omega⟩
    obtain ⟨exponent, originalTail⟩ :=
      triple_odd_constantTail (w := 3 * a) (by omega) tripleOdd
    have tail :
        IsConstantTail (9 * a) (embeddedValue (R (3 * a))) exponent 1 := by
      have stateShape : 3 * (3 * a) = 9 * a := by omega
      rw [stateShape] at originalTail
      exact originalTail
    have divisible : 9 * a + 1 = 4 * ((9 * a + 1) / 4) := by
      omega
    have exponentLarge : 2 ≤ exponent :=
      tail.exponentAtLeastTwo_of_raw_divisible_by_four divisible
    have expandingP : A (Q a 1 0) = 3 * a := by
      simpa [Q] using A_Q aPositive (Or.inl rfl) (by omega : 1 ≤ 1)
    have common : B (Q a 1 0) = R (3 * a) := by
      unfold B
      rw [expandingP]
    have expandingK : A (Q (3 * a) 1 0) = 9 * a := by
      rw [A_Q (by omega : 0 < 3 * a) (Or.inl rfl) (by omega : 1 ≤ 1)]
      simp [Q]
      omega
    refine ⟨exponent, exponentLarge, ?_, ?_⟩
    · rw [tailZero]
      change A (Q (3 * a) 1 0) =
        Q (embeddedValue (B (Q a 1 0))) exponent 1
      rw [expandingK, common]
      exact tail.equation
    · rw [tailZero]
      change B (Q (3 * a) 1 0) =
        Q (embeddedValue (B (Q a 1 0))) (exponent - 1) 1
      have commonR : R (A (Q a 1 0)) = R (3 * a) := by
        simpa [B] using common
      unfold B
      rw [expandingK, commonR, tail.equation]
      exact R_Q tail.positive tail.bit exponentLarge
  · subst tailBit
    have phaseOne : sourceASelectingBit z = 1 := tailOne
    have aMod : a % 4 = 1 := by
      exact embeddedValue_mod_four_of_selectingBit_one phaseOne
    have tripleOdd : OddNat (3 * a) := by
      obtain ⟨half, aShape⟩ := aOdd
      exact ⟨3 * half + 1, by dsimp [a] at aShape ⊢; omega⟩
    obtain ⟨exponent, originalTail⟩ :=
      triple_odd_minus_one_constantTail
        (w := 3 * a) (by omega) tripleOdd
    let commonValue := 3 * a - 1
    have commonPositive : 0 < commonValue := by
      dsimp [commonValue]
      omega
    have commonEven : commonValue % 2 = 0 := by
      dsimp [commonValue]
      obtain ⟨half, aShape⟩ := aOdd
      omega
    have remainderEquality : R (6 * a - 1) = R commonValue := by
      have appended := R_double_append_opposite
        commonPositive (Or.inr rfl) (by omega : commonValue % 2 ≠ 1)
      rw [show 2 * commonValue + 1 = 6 * a - 1 by
        dsimp [commonValue]; omega] at appended
      exact appended
    have tail :
        IsConstantTail (9 * a - 1)
          (embeddedValue (R commonValue)) exponent 0 := by
      have stateShape : 3 * (3 * a) - 1 = 9 * a - 1 := by omega
      have argumentShape : 2 * (3 * a) - 1 = 6 * a - 1 := by omega
      rw [stateShape, argumentShape, remainderEquality] at originalTail
      exact originalTail
    have divisible : 9 * a - 1 = 4 * ((9 * a - 1) / 4) := by
      omega
    have exponentLarge : 2 ≤ exponent := by
      apply tail.exponentAtLeastTwo_of_raw_divisible_by_four
      simpa using divisible
    have expandingP : A (Q a 1 1) = 3 * a - 1 := by
      simpa [Q] using A_Q aPositive (Or.inr rfl) (by omega : 1 ≤ 1)
    have common : B (Q a 1 1) = R commonValue := by
      unfold B
      rw [expandingP]
    have expandingK : A (Q (3 * a) 1 1) = 9 * a - 1 := by
      rw [A_Q (by omega : 0 < 3 * a) (Or.inr rfl) (by omega : 1 ≤ 1)]
      simp [Q]
      omega
    refine ⟨exponent, exponentLarge, ?_, ?_⟩
    · rw [tailOne]
      change A (Q (3 * a) 1 1) =
        Q (embeddedValue (B (Q a 1 1))) exponent 0
      rw [expandingK, common]
      exact tail.equation
    · rw [tailOne]
      change B (Q (3 * a) 1 1) =
        Q (embeddedValue (B (Q a 1 1))) (exponent - 1) 0
      have commonR : R (A (Q a 1 1)) = R commonValue := by
        simpa [B] using common
      unfold B
      rw [expandingK, commonR, tail.equation]
      exact R_Q tail.positive tail.bit exponentLarge

/--
Section 21's game-theoretic closure of a long phase-match frame.  The
arithmetic hypotheses are deliberately explicit: the ordinary common child
drops below the minimum, its canonical coefficient source drops by the
universal return bound, and the lower continuation contains at least four
factors of two in its alternating core.
-/
theorem minimumSource_phaseMatchLong_impossible
    {source : Nat}
    (sourceLarge : 4 ≤ source)
    (minimum : MinimumDrawSource source)
    (initialDraw :
      Draw (Q (embeddedValue source) 1 (sourceASelectingBit source)))
    (frame : PhaseMatchAdjacentFrame source)
    (returnBound : 8 * B (A source) ≤ 9 * source + 3)
    (commonValueDrop :
      B (Q (embeddedValue (B (A source))) 1
        (sourceASelectingBit source)) < source)
    (longCore :
      ∃ quotient,
        alternatingCore
          (A (Q (embeddedValue (B (A source))) 1
            (sourceASelectingBit source))) = 16 * quotient) :
    False := by
  let tailBit := sourceASelectingBit source
  let z := B (A source)
  let parent := Q (embeddedValue (A source)) 1 (1 - tailBit)
  let p := Q (embeddedValue z) 1 tailBit
  let h := Q (embeddedValue z) 2 tailBit
  let c := B p
  let d := A p
  let k := A h
  dsimp [PhaseMatchAdjacentFrame] at frame
  have phase : sourceASelectingBit z = tailBit := by
    simpa [z, tailBit] using frame.1
  have parentB : B parent = p := by
    simpa [parent, p, z, tailBit] using frame.2.1
  have parentA : A parent = h := by
    simpa [parent, h, z, tailBit] using frame.2.2
  have firstStep := minimumSource_sourceLift_forces_next
    (by omega : 0 < source) minimum initialDraw
  have parentDraw : Draw parent := by
    simpa [parent, tailBit] using firstStep.2
  obtain ⟨next, move, nextDraw⟩ := parentDraw.has_draw_child
  have childDraw : Draw h ∨ Draw p := by
    rcases move.2 with nextA | nextB
    · subst next
      rw [parentA] at nextDraw
      exact Or.inl nextDraw
    · subst next
      rw [parentB] at nextDraw
      exact Or.inr nextDraw
  have commonEquation : B h = c := by
    dsimp [h, c, p]
    exact (B_Q_one_eq_two (embeddedValue_positive z)
      (embeddedValue_odd z) (sourceASelectingBit_is_bit source)).symm
  have commonNotLosing : ¬ Losing c := by
    rcases childDraw with hDraw | pDraw
    · rw [← commonEquation]
      exact hDraw.children_not_losing.2
    · dsimp [c]
      exact pDraw.children_not_losing.2
  have commonPositive : 0 < c := by
    by_cases commonZero : c = 0
    · apply False.elim
      apply commonNotLosing
      rw [commonZero]
      exact Losing.terminal
    · omega
  obtain ⟨rho, commonSource⟩ := stateHasSource_exists commonPositive
  have commonSourceCanonical :
      StateHasSource
        (B (Q (embeddedValue z) 1 (sourceASelectingBit z))) rho := by
    rw [phase]
    simpa [c, p] using commonSource
  have rhoDrop : rho < source :=
    phaseMatch_commonChild_source_strict sourceLarge returnBound
      commonSourceCanonical
  have commonNotDraw := minimum.not_draw_of_smaller commonSource rhoDrop
  have commonWinning := winning_of_not_draw_and_not_losing
    commonNotDraw commonNotLosing
  rcases childDraw with hDraw | pDraw
  · have highDraw : Draw k := by
      dsimp [k]
      apply hDraw.A_of_B_winning
      rw [commonEquation]
      exact commonWinning
    have tailData : Bit tailBit := by
      simpa [tailBit] using sourceASelectingBit_is_bit source
    have complementData : Bit (1 - tailBit) := by
      rcases tailData with tailZero | tailOne
      · right
        omega
      · left
        omega
    obtain ⟨exponent, exponentLarge, highA, highB⟩ :=
      phaseMatch_high_adjacent_pair (z := z) (tailBit := tailBit)
        tailData phase.symm
    have highEquation : k = Q (3 * embeddedValue z) 1 tailBit := by
      dsimp [k, h]
      simpa using A_Q (embeddedValue_positive z) tailData
        (by omega : 1 ≤ 2)
    have highATail :
        IsConstantTail
          (A (Q (3 * embeddedValue z) 1 tailBit))
          (embeddedValue c) exponent (1 - tailBit) := by
      exact ⟨embeddedValue_positive c, embeddedValue_odd c,
        by omega, complementData, by simpa [c, p] using highA⟩
    have highBTail :
        IsConstantTail
          (B (Q (3 * embeddedValue z) 1 tailBit))
          (embeddedValue c) (exponent - 1) (1 - tailBit) := by
      exact ⟨embeddedValue_positive c, embeddedValue_odd c,
        by omega, complementData, by simpa [c, p] using highB⟩
    have highASource : StateHasSource (A k) c := by
      rw [highEquation]
      exact ⟨0, exponent, 1 - tailBit, embeddedValue c,
        highATail, ⟨by simp⟩⟩
    have highBSource : StateHasSource (B k) c := by
      rw [highEquation]
      exact ⟨0, exponent - 1, 1 - tailBit, embeddedValue c,
        highBTail, ⟨by simp⟩⟩
    obtain ⟨next, move, nextDraw⟩ := highDraw.has_draw_child
    rcases move.2 with nextA | nextB
    · subst next
      exact minimum.not_draw_of_smaller highASource commonValueDrop nextDraw
    · subst next
      exact minimum.not_draw_of_smaller highBSource commonValueDrop nextDraw
  · have lowerDraw : Draw d := by
      dsimp [d]
      apply pDraw.A_of_B_winning
      simpa [c] using commonWinning
    have coreForD :
        ∃ quotient, alternatingCore d = 16 * quotient := by
      simpa [d, p, z, tailBit] using longCore
    have lowerSources := longAlternating_children_have_source coreForD
    have commonIsR : c = R d := by
      rfl
    have lowerASource : StateHasSource (A d) c := by
      rw [commonIsR]
      exact lowerSources.1
    have lowerBSource : StateHasSource (B d) c := by
      rw [commonIsR]
      exact lowerSources.2
    obtain ⟨next, move, nextDraw⟩ := lowerDraw.has_draw_child
    rcases move.2 with nextA | nextB
    · subst next
      exact minimum.not_draw_of_smaller lowerASource commonValueDrop nextDraw
    · subst next
      exact minimum.not_draw_of_smaller lowerBSource commonValueDrop nextDraw

private theorem phaseMatch_longCore_twenty_one (t : Nat) :
    ∃ quotient,
      alternatingCore
        (A (Q (embeddedValue (B (A (128 * t + 21)))) 1
          (sourceASelectingBit (128 * t + 21)))) = 16 * quotient := by
  refine ⟨243 * t + 41, ?_⟩
  have returned : B (A (128 * t + 21)) = 144 * t + 24 := by
    rw [show 128 * t + 21 = 16 * (2 * (4 * t) + 1) + 5 by omega,
      returnRow_five]
    omega
  have phase : sourceASelectingBit (128 * t + 21) = 1 := by
    unfold sourceASelectingBit
    omega
  rw [returned, phase]
  rw [show A (Q (embeddedValue (144 * t + 24)) 1 1) =
      1296 * t + 218 by
    simp [A, Q, embeddedValue_formula]
    omega]
  simp [alternatingCore, show (1296 * t + 218) % 2 = 0 by omega]
  omega

private theorem phaseMatch_longCore_sixty_three (t : Nat) :
    ∃ quotient,
      alternatingCore
        (A (Q (embeddedValue (B (A (128 * t + 63)))) 1
          (sourceASelectingBit (128 * t + 63)))) = 16 * quotient := by
  refine ⟨243 * t + 121, ?_⟩
  have returned : B (A (128 * t + 63)) = 144 * t + 71 := by
    rw [show 128 * t + 63 = 16 * (2 * (4 * t + 1) + 1) + 15 by omega,
      returnRow_fifteen]
    omega
  have phase : sourceASelectingBit (128 * t + 63) = 0 := by
    unfold sourceASelectingBit
    omega
  rw [returned, phase]
  rw [show A (Q (embeddedValue (144 * t + 71)) 1 0) =
      1296 * t + 645 by
    simp [A, Q, embeddedValue_formula]
    omega]
  simp [alternatingCore, show (1296 * t + 645) % 2 ≠ 0 by omega]
  omega

private theorem phaseMatch_longCore_sixty_four (t : Nat) :
    ∃ quotient,
      alternatingCore
        (A (Q (embeddedValue (B (A (128 * t + 64)))) 1
          (sourceASelectingBit (128 * t + 64)))) = 16 * quotient := by
  refine ⟨243 * t + 122, ?_⟩
  have returned : B (A (128 * t + 64)) = 144 * t + 72 := by
    rw [show 128 * t + 64 = 16 * (2 * (4 * t + 2)) by omega,
      returnRow_zero]
    omega
  have phase : sourceASelectingBit (128 * t + 64) = 1 := by
    unfold sourceASelectingBit
    omega
  rw [returned, phase]
  rw [show A (Q (embeddedValue (144 * t + 72)) 1 1) =
      1296 * t + 650 by
    simp [A, Q, embeddedValue_formula]
    omega]
  simp [alternatingCore, show (1296 * t + 650) % 2 = 0 by omega]
  omega

private theorem phaseMatch_longCore_one_hundred_six (t : Nat) :
    ∃ quotient,
      alternatingCore
        (A (Q (embeddedValue (B (A (128 * t + 106)))) 1
          (sourceASelectingBit (128 * t + 106)))) = 16 * quotient := by
  refine ⟨243 * t + 202, ?_⟩
  have returned : B (A (128 * t + 106)) = 144 * t + 119 := by
    rw [show 128 * t + 106 = 16 * (2 * (4 * t + 3)) + 10 by omega,
      returnRow_ten]
    omega
  have phase : sourceASelectingBit (128 * t + 106) = 0 := by
    unfold sourceASelectingBit
    omega
  rw [returned, phase]
  rw [show A (Q (embeddedValue (144 * t + 119)) 1 0) =
      1296 * t + 1077 by
    simp [A, Q, embeddedValue_formula]
    omega]
  simp [alternatingCore, show (1296 * t + 1077) % 2 ≠ 0 by omega]
  omega

/-- All four long-suffix phase-match subclasses of Section 21 are excluded
for arbitrary parameters, not merely over a checked finite range. -/
theorem minimumSource_phaseMatchLong_twenty_one
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 21)) :
    ¬ Draw
      (Q (embeddedValue (128 * t + 21)) 1
        (sourceASelectingBit (128 * t + 21))) := by
  intro initialDraw
  exact minimumSource_phaseMatchLong_impossible (by omega) minimum initialDraw
    (by
      simpa only [show 128 * t + 21 = 32 * (4 * t) + 21 by omega] using
        phaseMatchAdjacentFrame_twenty_one (4 * t))
    (by
      simpa only [show 128 * t + 21 = 32 * (4 * t) + 21 by omega] using
        phaseMatch_return_bound_twenty_one (4 * t))
    (phaseMatch_commonChild_valueDrop_twenty_one t)
    (phaseMatch_longCore_twenty_one t)

theorem minimumSource_phaseMatchLong_sixty_three
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 63)) :
    ¬ Draw
      (Q (embeddedValue (128 * t + 63)) 1
        (sourceASelectingBit (128 * t + 63))) := by
  intro initialDraw
  exact minimumSource_phaseMatchLong_impossible (by omega) minimum initialDraw
    (by
      simpa only [show 128 * t + 63 = 32 * (4 * t + 1) + 31 by omega] using
        phaseMatchAdjacentFrame_thirty_one (4 * t + 1))
    (by
      simpa only [show 128 * t + 63 = 32 * (4 * t + 1) + 31 by omega] using
        phaseMatch_return_bound_thirty_one (4 * t + 1))
    (phaseMatch_commonChild_valueDrop_sixty_three t)
    (phaseMatch_longCore_sixty_three t)

theorem minimumSource_phaseMatchLong_sixty_four
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 64)) :
    ¬ Draw
      (Q (embeddedValue (128 * t + 64)) 1
        (sourceASelectingBit (128 * t + 64))) := by
  intro initialDraw
  exact minimumSource_phaseMatchLong_impossible (by omega) minimum initialDraw
    (by
      simpa only [show 128 * t + 64 = 32 * (4 * t + 2) by omega] using
        phaseMatchAdjacentFrame_zero (4 * t + 2))
    (by
      simpa only [show 128 * t + 64 = 32 * (4 * t + 2) by omega] using
        phaseMatch_return_bound_zero (4 * t + 2))
    (phaseMatch_commonChild_valueDrop_sixty_four t)
    (phaseMatch_longCore_sixty_four t)

theorem minimumSource_phaseMatchLong_one_hundred_six
    {t : Nat} (minimum : MinimumDrawSource (128 * t + 106)) :
    ¬ Draw
      (Q (embeddedValue (128 * t + 106)) 1
        (sourceASelectingBit (128 * t + 106))) := by
  intro initialDraw
  exact minimumSource_phaseMatchLong_impossible (by omega) minimum initialDraw
    (by
      simpa only [show 128 * t + 106 = 32 * (4 * t + 3) + 10 by omega] using
        phaseMatchAdjacentFrame_ten (4 * t + 3))
    (by
      simpa only [show 128 * t + 106 = 32 * (4 * t + 3) + 10 by omega] using
        phaseMatch_return_bound_ten (4 * t + 3))
    (phaseMatch_commonChild_valueDrop_one_hundred_six t)
    (phaseMatch_longCore_one_hundred_six t)

end ThreeNPlusMinusOne
