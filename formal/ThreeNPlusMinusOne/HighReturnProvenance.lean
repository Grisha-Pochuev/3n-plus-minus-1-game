import ThreeNPlusMinusOne.HighValuationTransfer
import ThreeNPlusMinusOne.TokenProvenance
import ThreeNPlusMinusOne.OccurrenceRefinement

set_option autoImplicit false

/-!
# Retained-token payment for a long high return

This file formalizes the safe local alternative in the high-return lifecycle:
when the two WIN occurrences at the returned state and its contracting child
are already retained, their exact common-grandchild descendants replace them
with a strict proof-forest payment.  It deliberately does not assert how the
incoming pair is installed or carried to a later high return.
-/

namespace ThreeNPlusMinusOne

/-- The first common side of every long high return is a common grandchild of
the returned state itself. -/
theorem highReturn_long_first_commonGrandchild
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 5 ≤ exponent) :
    CommonGrandchild
      (B (A (Q coefficient (exponent - 1) tailBit)))
      (Q coefficient (exponent - 1) tailBit) := by
  refine ⟨Or.inr rfl, Or.inl ?_⟩
  exact highReturn_long_common_grandchild positive bit exponentLarge

/-- For `v≥7`, the next common side is likewise a common grandchild of the
already retained contracting-side occurrence. -/
theorem highReturn_long_second_commonGrandchild
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (bit : Bit tailBit)
    (exponentLarge : 7 ≤ exponent) :
    CommonGrandchild
      (B (A (B (Q coefficient (exponent - 1) tailBit))))
      (B (Q coefficient (exponent - 1) tailBit)) := by
  refine ⟨Or.inr rfl, Or.inl ?_⟩
  exact highReturn_v_ge7_common_side_child positive bit exponentLarge

/-- The retained-pair alternative of the red high-return obligation.  If the
incoming forest already holds exact WIN occurrences at `u` and `B(u)`, the
`v≥7` geometry replaces them by exact common-grandchild occurrences at `p`
and `b`, strictly lowering both individual heights and the same forest rank.
No fresh finite token is installed by this theorem. -/
theorem highReturn_long_retained_pair_rank_payment
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) (exponentLarge : 7 ≤ exponent)
    {before middle after : ProofForest}
    (returnedToken contractingToken : WinningToken)
    (returnedPosition :
      returnedToken.position = Q coefficient (exponent - 1) tailBit)
    (contractingPosition :
      contractingToken.position = B (Q coefficient (exponent - 1) tailBit)) :
    ∃ firstDescendant secondDescendant : WinningToken,
      firstDescendant.position =
          B (A (Q coefficient (exponent - 1) tailBit)) ∧
        secondDescendant.position =
          B (A (B (Q coefficient (exponent - 1) tailBit))) ∧
          firstDescendant.height < returnedToken.height ∧
            secondDescendant.height < contractingToken.height ∧
              proofTokenRank
                  (before ++ [ProofToken.winning firstDescendant] ++ middle ++
                    [ProofToken.winning secondDescendant] ++ after) <
                proofTokenRank
                  (before ++ [ProofToken.winning returnedToken] ++ middle ++
                    [ProofToken.winning contractingToken] ++ after) := by
  have contractingPositive :
      0 < B (Q coefficient (exponent - 1) tailBit) := by
    rw [← contractingPosition]
    exact contractingToken.positive
  have firstPositive :
      0 < B (A (Q coefficient (exponent - 1) tailBit)) := by
    rw [highReturn_long_common_grandchild positive bit (by omega : 5 ≤ exponent)]
    exact A_pos contractingPositive
  have secondPositive :
      0 < B (A (B (Q coefficient (exponent - 1) tailBit))) := by
    rw [highReturn_v_ge7_common_side_child positive bit exponentLarge]
    exact A_pos (highReturn_long_loss_sibling_positive positive odd bit
      (by omega : 6 ≤ exponent))
  have firstCommon :
      CommonGrandchild
        (B (A (Q coefficient (exponent - 1) tailBit)))
        returnedToken.position := by
    rw [returnedPosition]
    exact highReturn_long_first_commonGrandchild positive bit
      (by omega : 5 ≤ exponent)
  have secondCommon :
      CommonGrandchild
        (B (A (B (Q coefficient (exponent - 1) tailBit))))
        contractingToken.position := by
    rw [contractingPosition]
    exact highReturn_long_second_commonGrandchild positive bit exponentLarge
  exact proofToken_pair_common_grandchild_rank_payment
    returnedToken contractingToken firstPositive secondPositive firstCommon
      secondCommon

/-- The retained-pair replacement is admitted by the occurrence-level macro
relation as two explicit equal-base forest steps.  Thus the local payment is
not merely a numerical inequality: it is a legal sequence of replacements of
the named incoming occurrences.  Preservation of a semantic `Bad` predicate
along these two steps remains part of the open global refinement. -/
theorem highReturn_long_retained_pair_outer_steps
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) (exponentLarge : 7 ≤ exponent)
    {before middle after innerForest : ProofForest}
    (base : MacroConfiguration)
    (returnedToken contractingToken : WinningToken)
    (returnedPosition :
      returnedToken.position = Q coefficient (exponent - 1) tailBit)
    (contractingPosition :
      contractingToken.position = B (Q coefficient (exponent - 1) tailBit)) :
    ∃ firstDescendant secondDescendant : WinningToken,
      firstDescendant.position =
          B (A (Q coefficient (exponent - 1) tailBit)) ∧
        secondDescendant.position =
          B (A (B (Q coefficient (exponent - 1) tailBit))) ∧
          OccurrenceMacroStep
            { base := base
              outerForest :=
                before ++ [ProofToken.winning firstDescendant] ++ middle ++
                  [ProofToken.winning secondDescendant] ++ after
              innerForest := innerForest }
            { base := base
              outerForest :=
                before ++ [ProofToken.winning firstDescendant] ++ middle ++
                  [ProofToken.winning contractingToken] ++ after
              innerForest := innerForest } ∧
            OccurrenceMacroStep
              { base := base
                outerForest :=
                  before ++ [ProofToken.winning firstDescendant] ++ middle ++
                    [ProofToken.winning contractingToken] ++ after
                innerForest := innerForest }
              { base := base
                outerForest :=
                  before ++ [ProofToken.winning returnedToken] ++ middle ++
                    [ProofToken.winning contractingToken] ++ after
                innerForest := innerForest } := by
  obtain ⟨firstDescendant, secondDescendant, firstPosition, secondPosition,
    firstLower, secondLower, _⟩ :=
    highReturn_long_retained_pair_rank_payment
      (before := before) (middle := middle) (after := after)
      positive odd bit exponentLarge returnedToken contractingToken
      returnedPosition contractingPosition
  refine ⟨firstDescendant, secondDescendant, firstPosition, secondPosition,
    ?_, ?_⟩
  · refine OccurrenceMacroStep.outerForest
      (next :=
        { base := base
          outerForest :=
            before ++ [ProofToken.winning firstDescendant] ++ middle ++
              [ProofToken.winning secondDescendant] ++ after
          innerForest := innerForest })
      (current :=
        { base := base
          outerForest :=
            before ++ [ProofToken.winning firstDescendant] ++ middle ++
              [ProofToken.winning contractingToken] ++ after
          innerForest := innerForest })
      rfl rfl ?_
    simpa [List.append_assoc] using
      (proofTokenReplacement_single
        (before := before ++ [ProofToken.winning firstDescendant] ++ middle)
        (after := after)
        (parent := ProofToken.winning contractingToken)
        (child := ProofToken.winning secondDescendant)
        (by simpa [ProofToken.height] using secondLower))
  · refine OccurrenceMacroStep.outerForest
      (next :=
        { base := base
          outerForest :=
            before ++ [ProofToken.winning firstDescendant] ++ middle ++
              [ProofToken.winning contractingToken] ++ after
          innerForest := innerForest })
      (current :=
        { base := base
          outerForest :=
            before ++ [ProofToken.winning returnedToken] ++ middle ++
              [ProofToken.winning contractingToken] ++ after
          innerForest := innerForest })
      rfl rfl ?_
    simpa [List.append_assoc] using
      (proofTokenReplacement_single
        (before := before)
        (after := middle ++ [ProofToken.winning contractingToken] ++ after)
        (parent := ProofToken.winning returnedToken)
        (child := ProofToken.winning firstDescendant)
        (by simpa [ProofToken.height] using firstLower))

end ThreeNPlusMinusOne
