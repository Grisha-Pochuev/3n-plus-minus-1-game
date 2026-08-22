import ThreeNPlusMinusOne.HighReturnProvenance
import ThreeNPlusMinusOne.OccurrenceCertificates
import ThreeNPlusMinusOne.CertifiedOccurrenceRefinement

set_option autoImplicit false

/-!
# Data-level retained-token payment for a long high return

The occurrence-level high-return result keeps finite proof trees in `Prop`.
This companion records the same safe local alternative with certificate data in
`Type`: all descendants are selected from branches already stored in the two
incoming certificates.  It still does not create the incoming pair or prove
that a semantic lifecycle preserves it.
-/

namespace ThreeNPlusMinusOne

/-- The long `v≥7` retained-pair payment can be carried out in a forest of
data-level certificates.  Both common-grandchild descendants retain their
stored branch choices, rather than being reconstructed from a bare finite
outcome proposition. -/
theorem certifiedHighReturn_long_retained_pair_rank_payment
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) (exponentLarge : 7 ≤ exponent)
    {before middle after : CertifiedProofForest}
    (returnedToken contractingToken : CertifiedWinningToken)
    (returnedPosition :
      returnedToken.position = Q coefficient (exponent - 1) tailBit)
    (contractingPosition :
      contractingToken.position = B (Q coefficient (exponent - 1) tailBit)) :
    ∃ firstDescendant secondDescendant : CertifiedWinningToken,
      firstDescendant.position =
          B (A (Q coefficient (exponent - 1) tailBit)) ∧
        secondDescendant.position =
          B (A (B (Q coefficient (exponent - 1) tailBit))) ∧
          firstDescendant.height < returnedToken.height ∧
            secondDescendant.height < contractingToken.height ∧
              certifiedProofTokenRank
                  (before ++ [CertifiedProofToken.winning firstDescendant] ++
                    middle ++ [CertifiedProofToken.winning secondDescendant] ++
                      after) <
                certifiedProofTokenRank
                  (before ++ [CertifiedProofToken.winning returnedToken] ++
                    middle ++ [CertifiedProofToken.winning contractingToken] ++
                      after) := by
  have contractingPositive :
      0 < B (Q coefficient (exponent - 1) tailBit) := by
    rw [← contractingPosition]
    exact contractingToken.erase.positive
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
  exact certifiedProofToken_pair_common_grandchild_rank_payment
    returnedToken contractingToken firstPositive secondPositive firstCommon
      secondCommon

/-- The data-level retained-pair payment is realized by two named certified
forest replacements. This proves local no-reseed legality at the certificate
level; installation, carry, and semantic `Bad` preservation remain external
obligations. -/
theorem certifiedHighReturn_long_retained_pair_replacements
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) (exponentLarge : 7 ≤ exponent)
    {before middle after : CertifiedProofForest}
    (returnedToken contractingToken : CertifiedWinningToken)
    (returnedPosition :
      returnedToken.position = Q coefficient (exponent - 1) tailBit)
    (contractingPosition :
      contractingToken.position = B (Q coefficient (exponent - 1) tailBit)) :
    ∃ firstDescendant secondDescendant : CertifiedWinningToken,
      firstDescendant.position =
          B (A (Q coefficient (exponent - 1) tailBit)) ∧
        secondDescendant.position =
          B (A (B (Q coefficient (exponent - 1) tailBit))) ∧
          CertifiedProofTokenReplacement
            (before ++ [CertifiedProofToken.winning firstDescendant] ++ middle ++
              [CertifiedProofToken.winning secondDescendant] ++ after)
            (before ++ [CertifiedProofToken.winning firstDescendant] ++ middle ++
              [CertifiedProofToken.winning contractingToken] ++ after) ∧
            CertifiedProofTokenReplacement
              (before ++ [CertifiedProofToken.winning firstDescendant] ++ middle ++
                [CertifiedProofToken.winning contractingToken] ++ after)
              (before ++ [CertifiedProofToken.winning returnedToken] ++ middle ++
                [CertifiedProofToken.winning contractingToken] ++ after) := by
  have contractingPositive :
      0 < B (Q coefficient (exponent - 1) tailBit) := by
    rw [← contractingPosition]
    exact contractingToken.erase.positive
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
  obtain ⟨firstDescendant, firstPosition, firstBound⟩ :=
    returnedToken.common_grandchild firstPositive firstCommon
  obtain ⟨secondDescendant, secondPosition, secondBound⟩ :=
    contractingToken.common_grandchild secondPositive secondCommon
  have firstLower : firstDescendant.height < returnedToken.height := by
    omega
  have secondLower : secondDescendant.height < contractingToken.height := by
    omega
  refine ⟨firstDescendant, secondDescendant, firstPosition, secondPosition,
    ?_, ?_⟩
  · simpa [List.append_assoc] using
      (certifiedProofTokenReplacement_single
        (before := before ++ [CertifiedProofToken.winning firstDescendant] ++
          middle)
        (after := after)
        (parent := CertifiedProofToken.winning contractingToken)
        (child := CertifiedProofToken.winning secondDescendant)
        (by simpa [CertifiedProofToken.height] using secondLower))
  · simpa [List.append_assoc] using
      (certifiedProofTokenReplacement_single
        (before := before)
        (after := middle ++ [CertifiedProofToken.winning contractingToken] ++
          after)
        (parent := CertifiedProofToken.winning returnedToken)
        (child := CertifiedProofToken.winning firstDescendant)
        (by simpa [CertifiedProofToken.height] using firstLower))

/-- The two data-level retained-pair replacements are legal equal-base steps
of the data-level occurrence macro relation. Thus their local no-reseed
status survives erasure into the prior occurrence refinement as well. -/
theorem certifiedHighReturn_long_retained_pair_outer_steps
    {coefficient exponent tailBit : Nat}
    (positive : 0 < coefficient) (odd : OddNat coefficient)
    (bit : Bit tailBit) (exponentLarge : 7 ≤ exponent)
    {before middle after innerForest : CertifiedProofForest}
    (base : MacroConfiguration)
    (returnedToken contractingToken : CertifiedWinningToken)
    (returnedPosition :
      returnedToken.position = Q coefficient (exponent - 1) tailBit)
    (contractingPosition :
      contractingToken.position = B (Q coefficient (exponent - 1) tailBit)) :
    ∃ firstDescendant secondDescendant : CertifiedWinningToken,
      firstDescendant.position =
          B (A (Q coefficient (exponent - 1) tailBit)) ∧
        secondDescendant.position =
          B (A (B (Q coefficient (exponent - 1) tailBit))) ∧
          CertifiedOccurrenceMacroStep
            { base := base
              outerForest :=
                before ++ [CertifiedProofToken.winning firstDescendant] ++
                  middle ++ [CertifiedProofToken.winning secondDescendant] ++
                    after
              innerForest := innerForest }
            { base := base
              outerForest :=
                before ++ [CertifiedProofToken.winning firstDescendant] ++
                  middle ++ [CertifiedProofToken.winning contractingToken] ++
                    after
              innerForest := innerForest } ∧
            CertifiedOccurrenceMacroStep
              { base := base
                outerForest :=
                  before ++ [CertifiedProofToken.winning firstDescendant] ++
                    middle ++ [CertifiedProofToken.winning contractingToken] ++
                      after
                innerForest := innerForest }
              { base := base
                outerForest :=
                  before ++ [CertifiedProofToken.winning returnedToken] ++
                    middle ++ [CertifiedProofToken.winning contractingToken] ++
                      after
                innerForest := innerForest } := by
  obtain ⟨firstDescendant, secondDescendant, firstPosition, secondPosition,
    secondReplacement, firstReplacement⟩ :=
    certifiedHighReturn_long_retained_pair_replacements
      (before := before) (middle := middle) (after := after)
      positive odd bit exponentLarge returnedToken contractingToken
      returnedPosition contractingPosition
  refine ⟨firstDescendant, secondDescendant, firstPosition, secondPosition,
    ?_, ?_⟩
  · refine CertifiedOccurrenceMacroStep.outerForest
      (next :=
        { base := base
          outerForest :=
            before ++ [CertifiedProofToken.winning firstDescendant] ++ middle ++
              [CertifiedProofToken.winning secondDescendant] ++ after
          innerForest := innerForest })
      (current :=
        { base := base
          outerForest :=
            before ++ [CertifiedProofToken.winning firstDescendant] ++ middle ++
              [CertifiedProofToken.winning contractingToken] ++ after
          innerForest := innerForest })
      rfl rfl ?_
    exact secondReplacement
  · refine CertifiedOccurrenceMacroStep.outerForest
      (next :=
        { base := base
          outerForest :=
            before ++ [CertifiedProofToken.winning firstDescendant] ++ middle ++
              [CertifiedProofToken.winning contractingToken] ++ after
          innerForest := innerForest })
      (current :=
        { base := base
          outerForest :=
            before ++ [CertifiedProofToken.winning returnedToken] ++ middle ++
              [CertifiedProofToken.winning contractingToken] ++ after
          innerForest := innerForest })
      rfl rfl ?_
    exact firstReplacement

end ThreeNPlusMinusOne
