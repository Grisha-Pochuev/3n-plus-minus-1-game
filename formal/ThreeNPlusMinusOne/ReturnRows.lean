import ThreeNPlusMinusOne.LiftedReturn

set_option autoImplicit false

/-!
# Exact nondecreasing ordinary return rows (Section 19)
-/

namespace ThreeNPlusMinusOne

theorem returnRow_zero (t : Nat) :
    B (A (16 * t)) = 18 * t := by
  by_cases tZero : t = 0
  · subst t
    simp [A, B]
  · have tPositive : 0 < t := by omega
    rw [show A (16 * t) = 24 * t by simp [A]; omega]
    unfold B
    rw [show A (24 * t) = 36 * t by simp [A]; omega]
    rw [R_of_boundary (by omega)
      (by omega : (36 * t) % 2 = ((36 * t) / 2) % 2)]
    omega

theorem returnRow_five (t : Nat) :
    B (A (16 * t + 5)) = 18 * t + 6 := by
  rw [show A (16 * t + 5) = 24 * t + 8 by simp [A]; omega]
  unfold B
  rw [show A (24 * t + 8) = 36 * t + 12 by simp [A]; omega]
  rw [R_of_boundary (by omega)
    (by omega : (36 * t + 12) % 2 = ((36 * t + 12) / 2) % 2)]
  omega

theorem returnRow_ten (t : Nat) :
    B (A (16 * t + 10)) = 18 * t + 11 := by
  rw [show A (16 * t + 10) = 24 * t + 15 by simp [A]; omega]
  unfold B
  rw [show A (24 * t + 15) = 36 * t + 23 by simp [A]; omega]
  rw [R_of_boundary (by omega)
    (by omega : (36 * t + 23) % 2 = ((36 * t + 23) / 2) % 2)]
  omega

theorem returnRow_fifteen (t : Nat) :
    B (A (16 * t + 15)) = 18 * t + 17 := by
  rw [show A (16 * t + 15) = 24 * t + 23 by simp [A]; omega]
  unfold B
  rw [show A (24 * t + 23) = 36 * t + 35 by simp [A]; omega]
  rw [R_of_boundary (by omega)
    (by omega : (36 * t + 35) % 2 = ((36 * t + 35) / 2) % 2)]
  omega

theorem returnRow_zero_strict {t : Nat} (positive : 0 < t) :
    16 * t < B (A (16 * t)) := by
  rw [returnRow_zero]
  omega

theorem returnRow_five_strict (t : Nat) :
    16 * t + 5 < B (A (16 * t + 5)) := by
  rw [returnRow_five]
  omega

theorem returnRow_ten_strict (t : Nat) :
    16 * t + 10 < B (A (16 * t + 10)) := by
  rw [returnRow_ten]
  omega

theorem returnRow_fifteen_strict (t : Nat) :
    16 * t + 15 < B (A (16 * t + 15)) := by
  rw [returnRow_fifteen]
  omega

theorem returnPhase_match_zero (t : Nat) :
    sourceASelectingBit (B (A (32 * t))) =
      sourceASelectingBit (32 * t) := by
  rw [show 32 * t = 16 * (2 * t) by omega, returnRow_zero]
  unfold sourceASelectingBit
  omega

theorem returnPhase_match_ten (t : Nat) :
    sourceASelectingBit (B (A (32 * t + 10))) =
      sourceASelectingBit (32 * t + 10) := by
  rw [show 32 * t + 10 = 16 * (2 * t) + 10 by omega, returnRow_ten]
  unfold sourceASelectingBit
  omega

theorem returnPhase_match_twenty_one (t : Nat) :
    sourceASelectingBit (B (A (32 * t + 21))) =
      sourceASelectingBit (32 * t + 21) := by
  rw [show 32 * t + 21 = 16 * (2 * t + 1) + 5 by omega,
    returnRow_five]
  unfold sourceASelectingBit
  omega

theorem returnPhase_match_thirty_one (t : Nat) :
    sourceASelectingBit (B (A (32 * t + 31))) =
      sourceASelectingBit (32 * t + 31) := by
  rw [show 32 * t + 31 = 16 * (2 * t + 1) + 15 by omega,
    returnRow_fifteen]
  unfold sourceASelectingBit
  omega

theorem returnPhase_mismatch_five (t : Nat) :
    sourceASelectingBit (B (A (32 * t + 5))) ≠
      sourceASelectingBit (32 * t + 5) := by
  rw [show 32 * t + 5 = 16 * (2 * t) + 5 by omega, returnRow_five]
  unfold sourceASelectingBit
  omega

theorem returnPhase_mismatch_fifteen (t : Nat) :
    sourceASelectingBit (B (A (32 * t + 15))) ≠
      sourceASelectingBit (32 * t + 15) := by
  rw [show 32 * t + 15 = 16 * (2 * t) + 15 by omega,
    returnRow_fifteen]
  unfold sourceASelectingBit
  omega

theorem returnPhase_mismatch_sixteen (t : Nat) :
    sourceASelectingBit (B (A (32 * t + 16))) ≠
      sourceASelectingBit (32 * t + 16) := by
  rw [show 32 * t + 16 = 16 * (2 * t + 1) by omega, returnRow_zero]
  unfold sourceASelectingBit
  omega

theorem returnPhase_mismatch_twenty_six (t : Nat) :
    sourceASelectingBit (B (A (32 * t + 26))) ≠
      sourceASelectingBit (32 * t + 26) := by
  rw [show 32 * t + 26 = 16 * (2 * t + 1) + 10 by omega,
    returnRow_ten]
  unfold sourceASelectingBit
  omega

def MismatchAdjacentFrame (source : Nat) : Prop :=
  let tailBit := sourceASelectingBit source
  let returnedSource := B (A source)
  let parent := Q (embeddedValue (A source)) 1 (1 - tailBit)
  tailBit = 1 - sourceASelectingBit returnedSource ∧
    B parent = Q (embeddedValue returnedSource) 1 tailBit ∧
      A parent = Q (embeddedValue returnedSource) 2 tailBit

private theorem mismatchAdjacentFrame_of_expanding
    {source : Nat}
    (phase :
      sourceASelectingBit source =
        1 - sourceASelectingBit (B (A source)))
    (expanding :
      A (Q (embeddedValue (A source)) 1
          (1 - sourceASelectingBit source)) =
        Q (embeddedValue (B (A source))) 2
          (sourceASelectingBit source)) :
    MismatchAdjacentFrame source := by
  dsimp [MismatchAdjacentFrame]
  refine ⟨phase, ?_, expanding⟩
  unfold B
  rw [expanding]
  exact R_Q (embeddedValue_positive (B (A source)))
    (sourceASelectingBit_is_bit source) (by omega)

theorem mismatchAdjacentFrame_five (t : Nat) :
    MismatchAdjacentFrame (32 * t + 5) := by
  apply mismatchAdjacentFrame_of_expanding
  · rw [show 32 * t + 5 = 16 * (2 * t) + 5 by omega,
      returnRow_five]
    unfold sourceASelectingBit
    omega
  · rw [show 32 * t + 5 = 16 * (2 * t) + 5 by omega,
      returnRow_five]
    simp [A, Q, embeddedValue_formula, sourceASelectingBit]
    omega

theorem mismatchAdjacentFrame_fifteen (t : Nat) :
    MismatchAdjacentFrame (32 * t + 15) := by
  apply mismatchAdjacentFrame_of_expanding
  · rw [show 32 * t + 15 = 16 * (2 * t) + 15 by omega,
      returnRow_fifteen]
    unfold sourceASelectingBit
    omega
  · rw [show 32 * t + 15 = 16 * (2 * t) + 15 by omega,
      returnRow_fifteen]
    simp [A, Q, embeddedValue_formula, sourceASelectingBit]
    omega

theorem mismatchAdjacentFrame_sixteen (t : Nat) :
    MismatchAdjacentFrame (32 * t + 16) := by
  apply mismatchAdjacentFrame_of_expanding
  · rw [show 32 * t + 16 = 16 * (2 * t + 1) by omega,
      returnRow_zero]
    unfold sourceASelectingBit
    omega
  · rw [show 32 * t + 16 = 16 * (2 * t + 1) by omega,
      returnRow_zero]
    simp [A, Q, embeddedValue_formula, sourceASelectingBit]
    omega

theorem mismatchAdjacentFrame_twenty_six (t : Nat) :
    MismatchAdjacentFrame (32 * t + 26) := by
  apply mismatchAdjacentFrame_of_expanding
  · rw [show 32 * t + 26 = 16 * (2 * t + 1) + 10 by omega,
      returnRow_ten]
    unfold sourceASelectingBit
    omega
  · rw [show 32 * t + 26 = 16 * (2 * t + 1) + 10 by omega,
      returnRow_ten]
    simp [A, Q, embeddedValue_formula, sourceASelectingBit]
    omega

theorem mismatchReturnedSourceDrop_five (t : Nat) :
    B (B (A (32 * t + 5))) < 32 * t + 5 := by
  rw [show 32 * t + 5 = 16 * (2 * t) + 5 by omega, returnRow_five]
  have bound := R_le_half (A (36 * t + 6))
  unfold B
  rw [show 18 * (2 * t) + 6 = 36 * t + 6 by omega,
    show 16 * (2 * t) + 5 = 32 * t + 5 by omega]
  rw [show A (36 * t + 6) = 54 * t + 9 by simp [A]; omega] at bound ⊢
  omega

theorem mismatchReturnedSourceDrop_fifteen (t : Nat) :
    B (B (A (32 * t + 15))) < 32 * t + 15 := by
  rw [show 32 * t + 15 = 16 * (2 * t) + 15 by omega,
    returnRow_fifteen]
  have bound := R_le_half (A (36 * t + 17))
  unfold B
  rw [show 18 * (2 * t) + 17 = 36 * t + 17 by omega,
    show 16 * (2 * t) + 15 = 32 * t + 15 by omega]
  rw [show A (36 * t + 17) = 54 * t + 26 by simp [A]; omega] at bound ⊢
  omega

theorem mismatchReturnedSourceDrop_sixteen (t : Nat) :
    B (B (A (32 * t + 16))) < 32 * t + 16 := by
  rw [show 32 * t + 16 = 16 * (2 * t + 1) by omega, returnRow_zero]
  have bound := R_le_half (A (36 * t + 18))
  unfold B
  rw [show 18 * (2 * t + 1) = 36 * t + 18 by omega,
    show 16 * (2 * t + 1) = 32 * t + 16 by omega]
  rw [show A (36 * t + 18) = 54 * t + 27 by simp [A]; omega] at bound ⊢
  omega

theorem mismatchReturnedSourceDrop_twenty_six (t : Nat) :
    B (B (A (32 * t + 26))) < 32 * t + 26 := by
  rw [show 32 * t + 26 = 16 * (2 * t + 1) + 10 by omega,
    returnRow_ten]
  have bound := R_le_half (A (36 * t + 29))
  unfold B
  rw [show 18 * (2 * t + 1) + 11 = 36 * t + 29 by omega,
    show 16 * (2 * t + 1) + 10 = 32 * t + 26 by omega]
  rw [show A (36 * t + 29) = 54 * t + 44 by simp [A]; omega] at bound ⊢
  omega

end ThreeNPlusMinusOne
