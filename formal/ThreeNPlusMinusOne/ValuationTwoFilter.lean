import ThreeNPlusMinusOne.BSelectingTransfer

set_option autoImplicit false

/-!
# The valuation-two residue filter (Section 26, arithmetic front)
-/

namespace ThreeNPlusMinusOne

def transferredCore (source : Nat) : Nat := A (A (B (A source)))

def transferredSource (source : Nat) : Nat := B (transferredCore source)

/-- The exact exponent-two constant-tail frame of a B-selecting source
transition. -/
def BSelectingValuationTwo (source : Nat) : Prop :=
  IsConstantTail
    (A (Q (embeddedValue source) 1
      (1 - sourceASelectingBit source)))
    (embeddedValue (B source)) 2 (sourceASelectingBit source)

/-- The sixteen modulo-256 subclasses of the eight Section 23 rows. -/
inductive LengthTwoResidue256 : Nat → Prop
  | r10 (u : Nat) : LengthTwoResidue256 (256 * u + 10)
  | r31 (u : Nat) : LengthTwoResidue256 (256 * u + 31)
  | r32 (u : Nat) : LengthTwoResidue256 (256 * u + 32)
  | r53 (u : Nat) : LengthTwoResidue256 (256 * u + 53)
  | r74 (u : Nat) : LengthTwoResidue256 (256 * u + 74)
  | r95 (u : Nat) : LengthTwoResidue256 (256 * u + 95)
  | r96 (u : Nat) : LengthTwoResidue256 (256 * u + 96)
  | r117 (u : Nat) : LengthTwoResidue256 (256 * u + 117)
  | r138 (u : Nat) : LengthTwoResidue256 (256 * u + 138)
  | r159 (u : Nat) : LengthTwoResidue256 (256 * u + 159)
  | r160 (u : Nat) : LengthTwoResidue256 (256 * u + 160)
  | r181 (u : Nat) : LengthTwoResidue256 (256 * u + 181)
  | r202 (u : Nat) : LengthTwoResidue256 (256 * u + 202)
  | r223 (u : Nat) : LengthTwoResidue256 (256 * u + 223)
  | r224 (u : Nat) : LengthTwoResidue256 (256 * u + 224)
  | r245 (u : Nat) : LengthTwoResidue256 (256 * u + 245)

/-- Exactly the eight residue classes in which the transferred source does
not drop. -/
inductive ValuationTwoResidue256 : Nat → Prop
  | r10 (u : Nat) : ValuationTwoResidue256 (256 * u + 10)
  | r31 (u : Nat) : ValuationTwoResidue256 (256 * u + 31)
  | r53 (u : Nat) : ValuationTwoResidue256 (256 * u + 53)
  | r95 (u : Nat) : ValuationTwoResidue256 (256 * u + 95)
  | r160 (u : Nat) : ValuationTwoResidue256 (256 * u + 160)
  | r202 (u : Nat) : ValuationTwoResidue256 (256 * u + 202)
  | r224 (u : Nat) : ValuationTwoResidue256 (256 * u + 224)
  | r245 (u : Nat) : ValuationTwoResidue256 (256 * u + 245)

private theorem B_four_le_A_of_alternating_pair
    {value : Nat} (large : 2 ≤ A value)
    (alternating : A value % 2 ≠ (A value / 2) % 2) :
    4 * B value ≤ A value := by
  unfold B
  rw [R_of_alternates large alternating]
  have lower := R_le_half (A value / 2)
  omega

private theorem core_10 (u : Nat) :
    transferredCore (256 * u + 10) = 648 * u + 26 := by
  unfold transferredCore
  rw [show 256 * u + 10 = 16 * (16 * u) + 10 by omega,
    returnRow_ten]
  simp [A]
  omega

private theorem core_31 (u : Nat) :
    transferredCore (256 * u + 31) = 648 * u + 80 := by
  unfold transferredCore
  rw [show 256 * u + 31 = 16 * (16 * u + 1) + 15 by omega,
    returnRow_fifteen]
  simp [A]
  omega

private theorem core_32 (u : Nat) :
    transferredCore (256 * u + 32) = 648 * u + 81 := by
  unfold transferredCore
  rw [show 256 * u + 32 = 16 * (16 * u + 2) by omega,
    returnRow_zero]
  simp [A]
  omega

private theorem core_53 (u : Nat) :
    transferredCore (256 * u + 53) = 648 * u + 135 := by
  unfold transferredCore
  rw [show 256 * u + 53 = 16 * (16 * u + 3) + 5 by omega,
    returnRow_five]
  simp [A]
  omega

private theorem core_74 (u : Nat) :
    transferredCore (256 * u + 74) = 648 * u + 188 := by
  unfold transferredCore
  rw [show 256 * u + 74 = 16 * (16 * u + 4) + 10 by omega,
    returnRow_ten]
  simp [A]
  omega

private theorem core_95 (u : Nat) :
    transferredCore (256 * u + 95) = 648 * u + 242 := by
  unfold transferredCore
  rw [show 256 * u + 95 = 16 * (16 * u + 5) + 15 by omega,
    returnRow_fifteen]
  simp [A]
  omega

private theorem core_96 (u : Nat) :
    transferredCore (256 * u + 96) = 648 * u + 243 := by
  unfold transferredCore
  rw [show 256 * u + 96 = 16 * (16 * u + 6) by omega,
    returnRow_zero]
  simp [A]
  omega

private theorem core_117 (u : Nat) :
    transferredCore (256 * u + 117) = 648 * u + 297 := by
  unfold transferredCore
  rw [show 256 * u + 117 = 16 * (16 * u + 7) + 5 by omega,
    returnRow_five]
  simp [A]
  omega

private theorem core_138 (u : Nat) :
    transferredCore (256 * u + 138) = 648 * u + 350 := by
  unfold transferredCore
  rw [show 256 * u + 138 = 16 * (16 * u + 8) + 10 by omega,
    returnRow_ten]
  simp [A]
  omega

private theorem core_159 (u : Nat) :
    transferredCore (256 * u + 159) = 648 * u + 404 := by
  unfold transferredCore
  rw [show 256 * u + 159 = 16 * (16 * u + 9) + 15 by omega,
    returnRow_fifteen]
  simp [A]
  omega

private theorem core_160 (u : Nat) :
    transferredCore (256 * u + 160) = 648 * u + 405 := by
  unfold transferredCore
  rw [show 256 * u + 160 = 16 * (16 * u + 10) by omega,
    returnRow_zero]
  simp [A]
  omega

private theorem core_181 (u : Nat) :
    transferredCore (256 * u + 181) = 648 * u + 459 := by
  unfold transferredCore
  rw [show 256 * u + 181 = 16 * (16 * u + 11) + 5 by omega,
    returnRow_five]
  simp [A]
  omega

private theorem core_202 (u : Nat) :
    transferredCore (256 * u + 202) = 648 * u + 512 := by
  unfold transferredCore
  rw [show 256 * u + 202 = 16 * (16 * u + 12) + 10 by omega,
    returnRow_ten]
  simp [A]
  omega

private theorem core_223 (u : Nat) :
    transferredCore (256 * u + 223) = 648 * u + 566 := by
  unfold transferredCore
  rw [show 256 * u + 223 = 16 * (16 * u + 13) + 15 by omega,
    returnRow_fifteen]
  simp [A]
  omega

private theorem core_224 (u : Nat) :
    transferredCore (256 * u + 224) = 648 * u + 567 := by
  unfold transferredCore
  rw [show 256 * u + 224 = 16 * (16 * u + 14) by omega,
    returnRow_zero]
  simp [A]
  omega

private theorem core_245 (u : Nat) :
    transferredCore (256 * u + 245) = 648 * u + 621 := by
  unfold transferredCore
  rw [show 256 * u + 245 = 16 * (16 * u + 15) + 5 by omega,
    returnRow_five]
  simp [A]
  omega

theorem transferredSource_10 (u : Nat) :
    transferredSource (256 * u + 10) = 486 * u + 19 := by
  rw [transferredSource, core_10]
  unfold B
  rw [show A (648 * u + 26) = 972 * u + 39 by simp [A]; omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

theorem transferredSource_31 (u : Nat) :
    transferredSource (256 * u + 31) = 486 * u + 60 := by
  rw [transferredSource, core_31]
  unfold B
  rw [show A (648 * u + 80) = 972 * u + 120 by simp [A]; omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

theorem transferredSource_53 (u : Nat) :
    transferredSource (256 * u + 53) = 486 * u + 101 := by
  rw [transferredSource, core_53]
  unfold B
  rw [show A (648 * u + 135) = 972 * u + 203 by simp [A]; omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

theorem transferredSource_95 (u : Nat) :
    transferredSource (256 * u + 95) = 486 * u + 181 := by
  rw [transferredSource, core_95]
  unfold B
  rw [show A (648 * u + 242) = 972 * u + 363 by simp [A]; omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

theorem transferredSource_160 (u : Nat) :
    transferredSource (256 * u + 160) = 486 * u + 304 := by
  rw [transferredSource, core_160]
  unfold B
  rw [show A (648 * u + 405) = 972 * u + 608 by simp [A]; omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

theorem transferredSource_202 (u : Nat) :
    transferredSource (256 * u + 202) = 486 * u + 384 := by
  rw [transferredSource, core_202]
  unfold B
  rw [show A (648 * u + 512) = 972 * u + 768 by simp [A]; omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

theorem transferredSource_224 (u : Nat) :
    transferredSource (256 * u + 224) = 486 * u + 425 := by
  rw [transferredSource, core_224]
  unfold B
  rw [show A (648 * u + 567) = 972 * u + 851 by simp [A]; omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

theorem transferredSource_245 (u : Nat) :
    transferredSource (256 * u + 245) = 486 * u + 466 := by
  rw [transferredSource, core_245]
  unfold B
  rw [show A (648 * u + 621) = 972 * u + 932 by simp [A]; omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

private theorem valuationTwo_10 (u : Nat) :
    BSelectingValuationTwo (648 * u + 26) := by
  have yEquation : B (648 * u + 26) = 486 * u + 19 := by
    unfold B
    rw [show A (648 * u + 26) = 972 * u + 39 by simp [A]; omega]
    rw [R_of_boundary (by omega) (by omega)]
    omega
  refine ⟨embeddedValue_positive _, embeddedValue_odd _, by omega,
    sourceASelectingBit_is_bit _, ?_⟩
  rw [yEquation]
  simp [A, Q, embeddedValue_formula, sourceASelectingBit]
  omega

private theorem valuationTwo_31 (u : Nat) :
    BSelectingValuationTwo (648 * u + 80) := by
  have yEquation : B (648 * u + 80) = 486 * u + 60 := by
    unfold B
    rw [show A (648 * u + 80) = 972 * u + 120 by simp [A]; omega]
    rw [R_of_boundary (by omega) (by omega)]
    omega
  refine ⟨embeddedValue_positive _, embeddedValue_odd _, by omega,
    sourceASelectingBit_is_bit _, ?_⟩
  rw [yEquation]
  simp [A, Q, embeddedValue_formula, sourceASelectingBit]
  omega

private theorem valuationTwo_53 (u : Nat) :
    BSelectingValuationTwo (648 * u + 135) := by
  have yEquation : B (648 * u + 135) = 486 * u + 101 := by
    unfold B
    rw [show A (648 * u + 135) = 972 * u + 203 by simp [A]; omega]
    rw [R_of_boundary (by omega) (by omega)]
    omega
  refine ⟨embeddedValue_positive _, embeddedValue_odd _, by omega,
    sourceASelectingBit_is_bit _, ?_⟩
  rw [yEquation]
  simp [A, Q, embeddedValue_formula, sourceASelectingBit]
  omega

private theorem valuationTwo_95 (u : Nat) :
    BSelectingValuationTwo (648 * u + 242) := by
  have yEquation : B (648 * u + 242) = 486 * u + 181 := by
    unfold B
    rw [show A (648 * u + 242) = 972 * u + 363 by simp [A]; omega]
    rw [R_of_boundary (by omega) (by omega)]
    omega
  refine ⟨embeddedValue_positive _, embeddedValue_odd _, by omega,
    sourceASelectingBit_is_bit _, ?_⟩
  rw [yEquation]
  simp [A, Q, embeddedValue_formula, sourceASelectingBit]
  omega

private theorem valuationTwo_160 (u : Nat) :
    BSelectingValuationTwo (648 * u + 405) := by
  have yEquation : B (648 * u + 405) = 486 * u + 304 := by
    unfold B
    rw [show A (648 * u + 405) = 972 * u + 608 by simp [A]; omega]
    rw [R_of_boundary (by omega) (by omega)]
    omega
  refine ⟨embeddedValue_positive _, embeddedValue_odd _, by omega,
    sourceASelectingBit_is_bit _, ?_⟩
  rw [yEquation]
  simp [A, Q, embeddedValue_formula, sourceASelectingBit]
  omega

private theorem valuationTwo_202 (u : Nat) :
    BSelectingValuationTwo (648 * u + 512) := by
  have yEquation : B (648 * u + 512) = 486 * u + 384 := by
    unfold B
    rw [show A (648 * u + 512) = 972 * u + 768 by simp [A]; omega]
    rw [R_of_boundary (by omega) (by omega)]
    omega
  refine ⟨embeddedValue_positive _, embeddedValue_odd _, by omega,
    sourceASelectingBit_is_bit _, ?_⟩
  rw [yEquation]
  simp [A, Q, embeddedValue_formula, sourceASelectingBit]
  omega

private theorem valuationTwo_224 (u : Nat) :
    BSelectingValuationTwo (648 * u + 567) := by
  have yEquation : B (648 * u + 567) = 486 * u + 425 := by
    unfold B
    rw [show A (648 * u + 567) = 972 * u + 851 by simp [A]; omega]
    rw [R_of_boundary (by omega) (by omega)]
    omega
  refine ⟨embeddedValue_positive _, embeddedValue_odd _, by omega,
    sourceASelectingBit_is_bit _, ?_⟩
  rw [yEquation]
  simp [A, Q, embeddedValue_formula, sourceASelectingBit]
  omega

private theorem valuationTwo_245 (u : Nat) :
    BSelectingValuationTwo (648 * u + 621) := by
  have yEquation : B (648 * u + 621) = 486 * u + 466 := by
    unfold B
    rw [show A (648 * u + 621) = 972 * u + 932 by simp [A]; omega]
    rw [R_of_boundary (by omega) (by omega)]
    omega
  refine ⟨embeddedValue_positive _, embeddedValue_odd _, by omega,
    sourceASelectingBit_is_bit _, ?_⟩
  rw [yEquation]
  simp [A, Q, embeddedValue_formula, sourceASelectingBit]
  omega

private theorem valuationTwo_32_impossible (u : Nat) :
    ¬ BSelectingValuationTwo (648 * u + 81) := by
  intro frame
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 81) (by simp [A]; omega) (by simp [A]; omega)
  have equation := frame.equation
  simp [A, Q, embeddedValue_formula, sourceASelectingBit] at equation bound
  have bBound := A_double_le (B (648 * u + 81))
  omega

private theorem valuationTwo_74_impossible (u : Nat) :
    ¬ BSelectingValuationTwo (648 * u + 188) := by
  intro frame
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 188) (by simp [A]; omega) (by simp [A]; omega)
  have equation := frame.equation
  simp [A, Q, embeddedValue_formula, sourceASelectingBit] at equation bound
  have bBound := A_double_le (B (648 * u + 188))
  omega

private theorem valuationTwo_96_impossible (u : Nat) :
    ¬ BSelectingValuationTwo (648 * u + 243) := by
  intro frame
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 243) (by simp [A]; omega) (by simp [A]; omega)
  have equation := frame.equation
  simp [A, Q, embeddedValue_formula, sourceASelectingBit] at equation bound
  have bBound := A_double_le (B (648 * u + 243))
  omega

private theorem valuationTwo_117_impossible (u : Nat) :
    ¬ BSelectingValuationTwo (648 * u + 297) := by
  intro frame
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 297) (by simp [A]; omega) (by simp [A]; omega)
  have equation := frame.equation
  simp [A, Q, embeddedValue_formula, sourceASelectingBit] at equation bound
  have bBound := A_double_le (B (648 * u + 297))
  omega

private theorem valuationTwo_138_impossible (u : Nat) :
    ¬ BSelectingValuationTwo (648 * u + 350) := by
  intro frame
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 350) (by simp [A]; omega) (by simp [A]; omega)
  have equation := frame.equation
  simp [A, Q, embeddedValue_formula, sourceASelectingBit] at equation bound
  have bBound := A_double_le (B (648 * u + 350))
  omega

private theorem valuationTwo_159_impossible (u : Nat) :
    ¬ BSelectingValuationTwo (648 * u + 404) := by
  intro frame
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 404) (by simp [A]; omega) (by simp [A]; omega)
  have equation := frame.equation
  simp [A, Q, embeddedValue_formula, sourceASelectingBit] at equation bound
  have bBound := A_double_le (B (648 * u + 404))
  omega

private theorem valuationTwo_181_impossible (u : Nat) :
    ¬ BSelectingValuationTwo (648 * u + 459) := by
  intro frame
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 459) (by simp [A]; omega) (by simp [A]; omega)
  have equation := frame.equation
  simp [A, Q, embeddedValue_formula, sourceASelectingBit] at equation bound
  have bBound := A_double_le (B (648 * u + 459))
  omega

private theorem valuationTwo_223_impossible (u : Nat) :
    ¬ BSelectingValuationTwo (648 * u + 566) := by
  intro frame
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 566) (by simp [A]; omega) (by simp [A]; omega)
  have equation := frame.equation
  simp [A, Q, embeddedValue_formula, sourceASelectingBit] at equation bound
  have bBound := A_double_le (B (648 * u + 566))
  omega

theorem transferredSource_32_strict (u : Nat) :
    transferredSource (256 * u + 32) < 256 * u + 32 := by
  rw [transferredSource, core_32]
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 81) (by simp [A]; omega) (by simp [A]; omega)
  simp [A] at bound
  omega

theorem transferredSource_74_strict (u : Nat) :
    transferredSource (256 * u + 74) < 256 * u + 74 := by
  rw [transferredSource, core_74]
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 188) (by simp [A]; omega) (by simp [A]; omega)
  simp [A] at bound
  omega

theorem transferredSource_96_strict (u : Nat) :
    transferredSource (256 * u + 96) < 256 * u + 96 := by
  rw [transferredSource, core_96]
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 243) (by simp [A]; omega) (by simp [A]; omega)
  simp [A] at bound
  omega

theorem transferredSource_117_strict (u : Nat) :
    transferredSource (256 * u + 117) < 256 * u + 117 := by
  rw [transferredSource, core_117]
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 297) (by simp [A]; omega) (by simp [A]; omega)
  simp [A] at bound
  omega

theorem transferredSource_138_strict (u : Nat) :
    transferredSource (256 * u + 138) < 256 * u + 138 := by
  rw [transferredSource, core_138]
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 350) (by simp [A]; omega) (by simp [A]; omega)
  simp [A] at bound
  omega

theorem transferredSource_159_strict (u : Nat) :
    transferredSource (256 * u + 159) < 256 * u + 159 := by
  rw [transferredSource, core_159]
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 404) (by simp [A]; omega) (by simp [A]; omega)
  simp [A] at bound
  omega

theorem transferredSource_181_strict (u : Nat) :
    transferredSource (256 * u + 181) < 256 * u + 181 := by
  rw [transferredSource, core_181]
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 459) (by simp [A]; omega) (by simp [A]; omega)
  simp [A] at bound
  omega

theorem transferredSource_223_strict (u : Nat) :
    transferredSource (256 * u + 223) < 256 * u + 223 := by
  rw [transferredSource, core_223]
  have bound := B_four_le_A_of_alternating_pair
    (value := 648 * u + 566) (by simp [A]; omega) (by simp [A]; omega)
  simp [A] at bound
  omega

/-- First boxed equivalence of Section 26: within the eight Section 23 rows,
the transferred source survives precisely in the displayed eight classes. -/
theorem transferredSource_ge_iff_residue
    {source : Nat} (row : LengthTwoResidue256 source) :
    source ≤ transferredSource source ↔ ValuationTwoResidue256 source := by
  constructor
  · intro survives
    cases row with
    | r10 u => exact ValuationTwoResidue256.r10 u
    | r31 u => exact ValuationTwoResidue256.r31 u
    | r32 u =>
        have strict := transferredSource_32_strict u
        exact False.elim (by omega)
    | r53 u => exact ValuationTwoResidue256.r53 u
    | r74 u =>
        have strict := transferredSource_74_strict u
        exact False.elim (by omega)
    | r95 u => exact ValuationTwoResidue256.r95 u
    | r96 u =>
        have strict := transferredSource_96_strict u
        exact False.elim (by omega)
    | r117 u =>
        have strict := transferredSource_117_strict u
        exact False.elim (by omega)
    | r138 u =>
        have strict := transferredSource_138_strict u
        exact False.elim (by omega)
    | r159 u =>
        have strict := transferredSource_159_strict u
        exact False.elim (by omega)
    | r160 u => exact ValuationTwoResidue256.r160 u
    | r181 u =>
        have strict := transferredSource_181_strict u
        exact False.elim (by omega)
    | r202 u => exact ValuationTwoResidue256.r202 u
    | r223 u =>
        have strict := transferredSource_223_strict u
        exact False.elim (by omega)
    | r224 u => exact ValuationTwoResidue256.r224 u
    | r245 u => exact ValuationTwoResidue256.r245 u
  · intro survives
    cases survives with
    | r10 u => rw [transferredSource_10]; omega
    | r31 u => rw [transferredSource_31]; omega
    | r53 u => rw [transferredSource_53]; omega
    | r95 u => rw [transferredSource_95]; omega
    | r160 u => rw [transferredSource_160]; omega
    | r202 u => rw [transferredSource_202]; omega
    | r224 u => rw [transferredSource_224]; omega
    | r245 u => rw [transferredSource_245]; omega

/-- Second boxed equivalence of Section 26: on the same sixteen subclasses,
the B-selecting transition at the transferred core has exponent exactly two
precisely in the eight surviving residue classes. -/
theorem transferredValuationTwo_iff_residue
    {source : Nat} (row : LengthTwoResidue256 source) :
    BSelectingValuationTwo (transferredCore source) ↔
      ValuationTwoResidue256 source := by
  constructor
  · intro valuation
    cases row with
    | r10 u => exact ValuationTwoResidue256.r10 u
    | r31 u => exact ValuationTwoResidue256.r31 u
    | r32 u =>
        rw [core_32] at valuation
        exact False.elim (valuationTwo_32_impossible u valuation)
    | r53 u => exact ValuationTwoResidue256.r53 u
    | r74 u =>
        rw [core_74] at valuation
        exact False.elim (valuationTwo_74_impossible u valuation)
    | r95 u => exact ValuationTwoResidue256.r95 u
    | r96 u =>
        rw [core_96] at valuation
        exact False.elim (valuationTwo_96_impossible u valuation)
    | r117 u =>
        rw [core_117] at valuation
        exact False.elim (valuationTwo_117_impossible u valuation)
    | r138 u =>
        rw [core_138] at valuation
        exact False.elim (valuationTwo_138_impossible u valuation)
    | r159 u =>
        rw [core_159] at valuation
        exact False.elim (valuationTwo_159_impossible u valuation)
    | r160 u => exact ValuationTwoResidue256.r160 u
    | r181 u =>
        rw [core_181] at valuation
        exact False.elim (valuationTwo_181_impossible u valuation)
    | r202 u => exact ValuationTwoResidue256.r202 u
    | r223 u =>
        rw [core_223] at valuation
        exact False.elim (valuationTwo_223_impossible u valuation)
    | r224 u => exact ValuationTwoResidue256.r224 u
    | r245 u => exact ValuationTwoResidue256.r245 u
  · intro survives
    cases survives with
    | r10 u => rw [core_10]; exact valuationTwo_10 u
    | r31 u => rw [core_31]; exact valuationTwo_31 u
    | r53 u => rw [core_53]; exact valuationTwo_53 u
    | r95 u => rw [core_95]; exact valuationTwo_95 u
    | r160 u => rw [core_160]; exact valuationTwo_160 u
    | r202 u => rw [core_202]; exact valuationTwo_202 u
    | r224 u => rw [core_224]; exact valuationTwo_224 u
    | r245 u => rw [core_245]; exact valuationTwo_245 u

/-- The two numerical criteria in Section 26 are therefore equivalent. -/
theorem transferredSource_ge_iff_valuationTwo
    {source : Nat} (row : LengthTwoResidue256 source) :
    source ≤ transferredSource source ↔
      BSelectingValuationTwo (transferredCore source) := by
  rw [transferredSource_ge_iff_residue row,
    transferredValuationTwo_iff_residue row]

/-- The sixteen modulo-512 subclasses of the eight valuation-two rows. -/
inductive ValuationTwoResidue512 : Nat → Prop
  | r10 (u : Nat) : ValuationTwoResidue512 (512 * u + 10)
  | r31 (u : Nat) : ValuationTwoResidue512 (512 * u + 31)
  | r53 (u : Nat) : ValuationTwoResidue512 (512 * u + 53)
  | r95 (u : Nat) : ValuationTwoResidue512 (512 * u + 95)
  | r160 (u : Nat) : ValuationTwoResidue512 (512 * u + 160)
  | r202 (u : Nat) : ValuationTwoResidue512 (512 * u + 202)
  | r224 (u : Nat) : ValuationTwoResidue512 (512 * u + 224)
  | r245 (u : Nat) : ValuationTwoResidue512 (512 * u + 245)
  | r266 (u : Nat) : ValuationTwoResidue512 (512 * u + 266)
  | r287 (u : Nat) : ValuationTwoResidue512 (512 * u + 287)
  | r309 (u : Nat) : ValuationTwoResidue512 (512 * u + 309)
  | r351 (u : Nat) : ValuationTwoResidue512 (512 * u + 351)
  | r416 (u : Nat) : ValuationTwoResidue512 (512 * u + 416)
  | r458 (u : Nat) : ValuationTwoResidue512 (512 * u + 458)
  | r480 (u : Nat) : ValuationTwoResidue512 (512 * u + 480)
  | r501 (u : Nat) : ValuationTwoResidue512 (512 * u + 501)

/-- Exactly the eight Section 26 subclasses where the next source phase
matches the transferred-core phase. -/
inductive NextPhaseMatchResidue512 : Nat → Prop
  | r10 (u : Nat) : NextPhaseMatchResidue512 (512 * u + 10)
  | r31 (u : Nat) : NextPhaseMatchResidue512 (512 * u + 31)
  | r160 (u : Nat) : NextPhaseMatchResidue512 (512 * u + 160)
  | r202 (u : Nat) : NextPhaseMatchResidue512 (512 * u + 202)
  | r309 (u : Nat) : NextPhaseMatchResidue512 (512 * u + 309)
  | r351 (u : Nat) : NextPhaseMatchResidue512 (512 * u + 351)
  | r480 (u : Nat) : NextPhaseMatchResidue512 (512 * u + 480)
  | r501 (u : Nat) : NextPhaseMatchResidue512 (512 * u + 501)

/-- Splitting the modulo-256 survivor parameter by parity produces exactly
the sixteen modulo-512 rows above. -/
theorem ValuationTwoResidue256.to512
    {source : Nat} (row : ValuationTwoResidue256 source) :
    ValuationTwoResidue512 source := by
  cases row with
  | r10 u =>
      rcases even_or_odd u with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · simpa only [show 256 * (2 * v) + 10 = 512 * v + 10 by omega] using
          ValuationTwoResidue512.r10 v
      · simpa only [show 256 * (2 * v + 1) + 10 = 512 * v + 266 by omega] using
          ValuationTwoResidue512.r266 v
  | r31 u =>
      rcases even_or_odd u with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · simpa only [show 256 * (2 * v) + 31 = 512 * v + 31 by omega] using
          ValuationTwoResidue512.r31 v
      · simpa only [show 256 * (2 * v + 1) + 31 = 512 * v + 287 by omega] using
          ValuationTwoResidue512.r287 v
  | r53 u =>
      rcases even_or_odd u with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · simpa only [show 256 * (2 * v) + 53 = 512 * v + 53 by omega] using
          ValuationTwoResidue512.r53 v
      · simpa only [show 256 * (2 * v + 1) + 53 = 512 * v + 309 by omega] using
          ValuationTwoResidue512.r309 v
  | r95 u =>
      rcases even_or_odd u with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · simpa only [show 256 * (2 * v) + 95 = 512 * v + 95 by omega] using
          ValuationTwoResidue512.r95 v
      · simpa only [show 256 * (2 * v + 1) + 95 = 512 * v + 351 by omega] using
          ValuationTwoResidue512.r351 v
  | r160 u =>
      rcases even_or_odd u with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · simpa only [show 256 * (2 * v) + 160 = 512 * v + 160 by omega] using
          ValuationTwoResidue512.r160 v
      · simpa only [show 256 * (2 * v + 1) + 160 = 512 * v + 416 by omega] using
          ValuationTwoResidue512.r416 v
  | r202 u =>
      rcases even_or_odd u with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · simpa only [show 256 * (2 * v) + 202 = 512 * v + 202 by omega] using
          ValuationTwoResidue512.r202 v
      · simpa only [show 256 * (2 * v + 1) + 202 = 512 * v + 458 by omega] using
          ValuationTwoResidue512.r458 v
  | r224 u =>
      rcases even_or_odd u with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · simpa only [show 256 * (2 * v) + 224 = 512 * v + 224 by omega] using
          ValuationTwoResidue512.r224 v
      · simpa only [show 256 * (2 * v + 1) + 224 = 512 * v + 480 by omega] using
          ValuationTwoResidue512.r480 v
  | r245 u =>
      rcases even_or_odd u with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · simpa only [show 256 * (2 * v) + 245 = 512 * v + 245 by omega] using
          ValuationTwoResidue512.r245 v
      · simpa only [show 256 * (2 * v + 1) + 245 = 512 * v + 501 by omega] using
          ValuationTwoResidue512.r501 v

private theorem nextPhase_10 (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 10)) =
      sourceASelectingBit (transferredSource (512 * u + 10)) := by
  have coreEquation := core_10 (2 * u)
  have sourceEquation := transferredSource_10 (2 * u)
  have sourceShape : 256 * (2 * u) + 10 = 512 * u + 10 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_31 (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 31)) =
      sourceASelectingBit (transferredSource (512 * u + 31)) := by
  have coreEquation := core_31 (2 * u)
  have sourceEquation := transferredSource_31 (2 * u)
  have sourceShape : 256 * (2 * u) + 31 = 512 * u + 31 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_160 (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 160)) =
      sourceASelectingBit (transferredSource (512 * u + 160)) := by
  have coreEquation := core_160 (2 * u)
  have sourceEquation := transferredSource_160 (2 * u)
  have sourceShape : 256 * (2 * u) + 160 = 512 * u + 160 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_202 (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 202)) =
      sourceASelectingBit (transferredSource (512 * u + 202)) := by
  have coreEquation := core_202 (2 * u)
  have sourceEquation := transferredSource_202 (2 * u)
  have sourceShape : 256 * (2 * u) + 202 = 512 * u + 202 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_309 (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 309)) =
      sourceASelectingBit (transferredSource (512 * u + 309)) := by
  have coreEquation := core_53 (2 * u + 1)
  have sourceEquation := transferredSource_53 (2 * u + 1)
  have sourceShape :
      256 * (2 * u + 1) + 53 = 512 * u + 309 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_351 (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 351)) =
      sourceASelectingBit (transferredSource (512 * u + 351)) := by
  have coreEquation := core_95 (2 * u + 1)
  have sourceEquation := transferredSource_95 (2 * u + 1)
  have sourceShape :
      256 * (2 * u + 1) + 95 = 512 * u + 351 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_480 (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 480)) =
      sourceASelectingBit (transferredSource (512 * u + 480)) := by
  have coreEquation := core_224 (2 * u + 1)
  have sourceEquation := transferredSource_224 (2 * u + 1)
  have sourceShape :
      256 * (2 * u + 1) + 224 = 512 * u + 480 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_501 (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 501)) =
      sourceASelectingBit (transferredSource (512 * u + 501)) := by
  have coreEquation := core_245 (2 * u + 1)
  have sourceEquation := transferredSource_245 (2 * u + 1)
  have sourceShape :
      256 * (2 * u + 1) + 245 = 512 * u + 501 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_53_ne (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 53)) ≠
      sourceASelectingBit (transferredSource (512 * u + 53)) := by
  have coreEquation := core_53 (2 * u)
  have sourceEquation := transferredSource_53 (2 * u)
  have sourceShape : 256 * (2 * u) + 53 = 512 * u + 53 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_95_ne (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 95)) ≠
      sourceASelectingBit (transferredSource (512 * u + 95)) := by
  have coreEquation := core_95 (2 * u)
  have sourceEquation := transferredSource_95 (2 * u)
  have sourceShape : 256 * (2 * u) + 95 = 512 * u + 95 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_224_ne (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 224)) ≠
      sourceASelectingBit (transferredSource (512 * u + 224)) := by
  have coreEquation := core_224 (2 * u)
  have sourceEquation := transferredSource_224 (2 * u)
  have sourceShape : 256 * (2 * u) + 224 = 512 * u + 224 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_245_ne (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 245)) ≠
      sourceASelectingBit (transferredSource (512 * u + 245)) := by
  have coreEquation := core_245 (2 * u)
  have sourceEquation := transferredSource_245 (2 * u)
  have sourceShape : 256 * (2 * u) + 245 = 512 * u + 245 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_266_ne (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 266)) ≠
      sourceASelectingBit (transferredSource (512 * u + 266)) := by
  have coreEquation := core_10 (2 * u + 1)
  have sourceEquation := transferredSource_10 (2 * u + 1)
  have sourceShape :
      256 * (2 * u + 1) + 10 = 512 * u + 266 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_287_ne (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 287)) ≠
      sourceASelectingBit (transferredSource (512 * u + 287)) := by
  have coreEquation := core_31 (2 * u + 1)
  have sourceEquation := transferredSource_31 (2 * u + 1)
  have sourceShape :
      256 * (2 * u + 1) + 31 = 512 * u + 287 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_416_ne (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 416)) ≠
      sourceASelectingBit (transferredSource (512 * u + 416)) := by
  have coreEquation := core_160 (2 * u + 1)
  have sourceEquation := transferredSource_160 (2 * u + 1)
  have sourceShape :
      256 * (2 * u + 1) + 160 = 512 * u + 416 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

private theorem nextPhase_458_ne (u : Nat) :
    sourceASelectingBit (transferredCore (512 * u + 458)) ≠
      sourceASelectingBit (transferredSource (512 * u + 458)) := by
  have coreEquation := core_202 (2 * u + 1)
  have sourceEquation := transferredSource_202 (2 * u + 1)
  have sourceShape :
      256 * (2 * u + 1) + 202 = 512 * u + 458 := by omega
  rw [sourceShape] at coreEquation sourceEquation
  rw [coreEquation, sourceEquation]
  simp [sourceASelectingBit]
  omega

/-- Final boxed phase split of Section 26. -/
theorem transferredNextPhaseMatch_iff_residue
    {source : Nat} (row : ValuationTwoResidue512 source) :
    sourceASelectingBit (transferredCore source) =
        sourceASelectingBit (transferredSource source) ↔
      NextPhaseMatchResidue512 source := by
  constructor
  · intro phaseMatch
    cases row with
    | r10 u => exact NextPhaseMatchResidue512.r10 u
    | r31 u => exact NextPhaseMatchResidue512.r31 u
    | r53 u => exact False.elim (nextPhase_53_ne u phaseMatch)
    | r95 u => exact False.elim (nextPhase_95_ne u phaseMatch)
    | r160 u => exact NextPhaseMatchResidue512.r160 u
    | r202 u => exact NextPhaseMatchResidue512.r202 u
    | r224 u => exact False.elim (nextPhase_224_ne u phaseMatch)
    | r245 u => exact False.elim (nextPhase_245_ne u phaseMatch)
    | r266 u => exact False.elim (nextPhase_266_ne u phaseMatch)
    | r287 u => exact False.elim (nextPhase_287_ne u phaseMatch)
    | r309 u => exact NextPhaseMatchResidue512.r309 u
    | r351 u => exact NextPhaseMatchResidue512.r351 u
    | r416 u => exact False.elim (nextPhase_416_ne u phaseMatch)
    | r458 u => exact False.elim (nextPhase_458_ne u phaseMatch)
    | r480 u => exact NextPhaseMatchResidue512.r480 u
    | r501 u => exact NextPhaseMatchResidue512.r501 u
  · intro phaseRow
    cases phaseRow with
    | r10 u => exact nextPhase_10 u
    | r31 u => exact nextPhase_31 u
    | r160 u => exact nextPhase_160 u
    | r202 u => exact nextPhase_202 u
    | r309 u => exact nextPhase_309 u
    | r351 u => exact nextPhase_351 u
    | r480 u => exact nextPhase_480 u
    | r501 u => exact nextPhase_501 u

/-- The phase classification is exhaustive directly from the modulo-256
valuation-two classification. -/
theorem transferredNextPhaseMatch_iff_residue_of256
    {source : Nat} (row : ValuationTwoResidue256 source) :
    sourceASelectingBit (transferredCore source) =
        sourceASelectingBit (transferredSource source) ↔
      NextPhaseMatchResidue512 source :=
  transferredNextPhaseMatch_iff_residue row.to512

end ThreeNPlusMinusOne
