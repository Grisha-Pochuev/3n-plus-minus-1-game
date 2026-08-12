import ThreeNPlusMinusOne.ReturnRows

set_option autoImplicit false

/-!
# Outcome closure of the phase-mismatch large diamond (Section 20)
-/

namespace ThreeNPlusMinusOne

private theorem R_four_one_of_even {value : Nat}
    (positive : 0 < value) (even : value % 2 = 0) :
    R (4 * value + 1) = value := by
  rw [R_of_alternates (by omega) (by omega)]
  rw [show (4 * value + 1) / 2 = 2 * value by omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

private theorem R_four_two_of_odd {value : Nat}
    (odd : value % 2 = 1) : R (4 * value + 2) = value := by
  rw [R_of_alternates (by omega) (by omega)]
  rw [show (4 * value + 2) / 2 = 2 * value + 1 by omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

private theorem R_eight_five_of_even {value : Nat}
    (positive : 0 < value) (even : value % 2 = 0) :
    R (8 * value + 5) = R value := by
  rw [R_of_alternates (by omega) (by omega)]
  rw [show (8 * value + 5) / 2 = 4 * value + 2 by omega]
  rw [R_of_alternates (by omega) (by omega)]
  rw [show (4 * value + 2) / 2 = 2 * value + 1 by omega]
  rw [R_of_alternates (by omega) (by omega)]
  rw [show (2 * value + 1) / 2 = value by omega]

private theorem R_eight_two_of_odd {value : Nat}
    (odd : value % 2 = 1) : R (8 * value + 2) = R value := by
  rw [R_of_alternates (by omega) (by omega)]
  rw [show (8 * value + 2) / 2 = 4 * value + 1 by omega]
  rw [R_of_alternates (by omega) (by omega)]
  rw [show (4 * value + 1) / 2 = 2 * value by omega]
  rw [R_of_alternates (by omega) (by omega)]
  rw [show (2 * value) / 2 = value by omega]

private theorem R_eight_five_of_odd {value : Nat}
    (odd : value % 2 = 1) : R (8 * value + 5) = value := by
  rw [R_of_alternates (by omega) (by omega)]
  rw [show (8 * value + 5) / 2 = 4 * value + 2 by omega]
  rw [R_of_alternates (by omega) (by omega)]
  rw [show (4 * value + 2) / 2 = 2 * value + 1 by omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

private theorem R_eight_two_of_even {value : Nat}
    (positive : 0 < value) (even : value % 2 = 0) :
    R (8 * value + 2) = value := by
  rw [R_of_alternates (by omega) (by omega)]
  rw [show (8 * value + 2) / 2 = 4 * value + 1 by omega]
  rw [R_of_alternates (by omega) (by omega)]
  rw [show (4 * value + 1) / 2 = 2 * value by omega]
  rw [R_of_boundary (by omega) (by omega)]
  omega

/-- Section 20 large-diamond identity in the valuation-two row. -/
theorem largeDiamond_identity_valuation_two
    {a b tailBit : Nat} (aPositive : 0 < a) (bPositive : 0 < b)
    (bOdd : OddNat b) (bit : Bit tailBit)
    (valuation : 3 * a + 1 - 2 * tailBit = 4 * b) :
    B (Q (3 * a) 1 tailBit) =
      A (Q b 1 (1 - tailBit)) := by
  have complementBit : Bit (1 - tailBit) := by
    rcases bit with hzero | hone
    · right
      omega
    · left
      omega
  have leftA :
      A (Q (3 * a) 1 tailBit) = Q (9 * a) 0 tailBit := by
    rw [A_Q (coefficient := 3 * a) (exponent := 1)
      (tailBit := tailBit) (by omega) bit (by omega)]
    rw [show 3 * (3 * a) = 9 * a by omega]
  have rightA :
      A (Q b 1 (1 - tailBit)) = Q (3 * b) 0 (1 - tailBit) :=
    A_Q bPositive complementBit (by omega)
  unfold B
  rw [leftA, rightA]
  obtain ⟨bHalf, bShape⟩ := bOdd
  rcases bit with hzero | hone
  · rw [hzero] at valuation ⊢
    simp [Q] at valuation ⊢
    have valuePositive : 0 < 3 * b - 1 := by omega
    have valueEven : (3 * b - 1) % 2 = 0 := by omega
    rw [show 9 * a = 4 * (3 * b - 1) + 1 by omega]
    exact R_four_one_of_even valuePositive valueEven
  · rw [hone] at valuation ⊢
    simp [Q] at valuation ⊢
    have valueOdd : (3 * b) % 2 = 1 := by omega
    rw [show 9 * a - 1 = 4 * (3 * b) + 2 by omega]
    exact R_four_two_of_odd valueOdd

/-- Section 20 large-diamond identity in the valuation-three row. -/
theorem largeDiamond_identity_valuation_three
    {a b tailBit : Nat} (aPositive : 0 < a) (bPositive : 0 < b)
    (bOdd : OddNat b) (bit : Bit tailBit)
    (valuation : 3 * a + 1 - 2 * tailBit = 8 * b) :
    B (Q (3 * a) 1 tailBit) =
      B (Q b 2 (1 - tailBit)) := by
  have complementBit : Bit (1 - tailBit) := by
    rcases bit with hzero | hone
    · right
      omega
    · left
      omega
  have leftA :
      A (Q (3 * a) 1 tailBit) = Q (9 * a) 0 tailBit := by
    rw [A_Q (coefficient := 3 * a) (exponent := 1)
      (tailBit := tailBit) (by omega) bit (by omega)]
    rw [show 3 * (3 * a) = 9 * a by omega]
  have rightA :
      A (Q b 2 (1 - tailBit)) = Q (3 * b) 1 (1 - tailBit) := by
    simpa using A_Q bPositive complementBit (by omega : 1 ≤ 2)
  unfold B
  rw [leftA, rightA]
  obtain ⟨bHalf, bShape⟩ := bOdd
  rcases bit with hzero | hone
  · rw [hzero] at valuation ⊢
    simp [Q] at valuation ⊢
    let value := 3 * b - 1
    have valuePositive : 0 < value := by dsimp [value]; omega
    have valueEven : value % 2 = 0 := by dsimp [value]; omega
    have appended : R (2 * value + 1) = R value :=
      R_double_append_opposite valuePositive (Or.inr rfl) (by omega)
    rw [show 9 * a = 8 * value + 5 by dsimp [value]; omega]
    rw [R_eight_five_of_even valuePositive valueEven]
    rw [show 3 * b * 2 - 1 = 2 * value + 1 by
      dsimp [value]; omega]
    exact appended.symm
  · rw [hone] at valuation ⊢
    simp [Q] at valuation ⊢
    let value := 3 * b
    have valuePositive : 0 < value := by dsimp [value]; omega
    have valueOdd : value % 2 = 1 := by dsimp [value]; omega
    have appended : R (2 * value) = R value :=
      R_double_append_opposite valuePositive (Or.inl rfl) (by omega)
    rw [show 9 * a - 1 = 8 * value + 2 by dsimp [value]; omega]
    rw [R_eight_two_of_odd valueOdd]
    rw [show 3 * b * 2 = 2 * value by
      dsimp [value]; omega]
    exact appended.symm

/-- Section 20 large-diamond identity for every valuation at least four. -/
theorem largeDiamond_identity_valuation_high
    {a b exponent tailBit : Nat}
    (aPositive : 0 < a) (bPositive : 0 < b)
    (bOdd : OddNat b) (bit : Bit tailBit)
    (exponentLarge : 4 ≤ exponent)
    (valuation :
      3 * a + 1 - 2 * tailBit = 2 ^ exponent * b) :
    B (Q (3 * a) 1 tailBit) =
      B (Q b (exponent - 1) (1 - tailBit)) := by
  obtain ⟨rest, exponentShape⟩ : ∃ rest, exponent = rest + 4 :=
    ⟨exponent - 4, by omega⟩
  subst exponent
  have complementBit : Bit (1 - tailBit) := by
    rcases bit with hzero | hone
    · right
      omega
    · left
      omega
  have tripleOdd : OddNat (3 * b) := by
    obtain ⟨half, bShape⟩ := bOdd
    exact ⟨3 * half + 1, by omega⟩
  have leftA :
      A (Q (3 * a) 1 tailBit) = Q (9 * a) 0 tailBit := by
    rw [A_Q (coefficient := 3 * a) (exponent := 1)
      (tailBit := tailBit) (by omega) bit (by omega)]
    rw [show 3 * (3 * a) = 9 * a by omega]
  have rightB :
      B (Q b (rest + 4 - 1) (1 - tailBit)) =
        Q (3 * b) (rest + 1) (1 - tailBit) := by
    rw [B_Q bPositive complementBit (by omega)]
    congr 2
  let value := Q (3 * b) (rest + 1) (1 - tailBit)
  have valueTail :
      IsConstantTail value (3 * b) (rest + 1) (1 - tailBit) :=
    ⟨by omega, tripleOdd, by omega, complementBit, rfl⟩
  have valuePositive : 0 < value := valueTail.state_positive
  unfold B
  rw [leftA]
  change R (Q (9 * a) 0 tailBit) =
    B (Q b (rest + 4 - 1) (1 - tailBit))
  rw [rightB]
  change R (Q (9 * a) 0 tailBit) = value
  have powerShape : 2 ^ (rest + 4) = 8 * 2 ^ (rest + 1) := by
    simp [Nat.pow_succ, Nat.mul_comm] <;> omega
  obtain ⟨bHalf, bShape⟩ := bOdd
  rcases bit with hzero | hone
  · rw [hzero] at valuation ⊢
    simp [Q] at valuation ⊢
    let base := b * 2 ^ (rest + 1)
    have valuationBase : 3 * a + 1 = 8 * base := by
      rw [powerShape] at valuation
      simpa [base, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        using valuation
    have valueBase : value = 3 * base - 1 := by
      simp [value, Q, hzero, base, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    have valueOdd : value % 2 = 1 := by
      have baseEven : base % 2 = 0 := by
        have baseTwice : base = 2 * (b * 2 ^ rest) := by
          simp [base, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
        rw [baseTwice]
        omega
      rw [valueBase]
      omega
    have rawShape : 9 * a = 8 * value + 5 := by
      omega
    rw [rawShape]
    exact R_eight_five_of_odd valueOdd
  · rw [hone] at valuation ⊢
    simp [Q] at valuation ⊢
    let base := b * 2 ^ (rest + 1)
    have valuationBase : 3 * a - 1 = 8 * base := by
      rw [powerShape] at valuation
      simpa [base, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
        using valuation
    have valueBase : value = 3 * base := by
      simp [value, Q, hone, base, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm]
    have valueEven : value % 2 = 0 := by
      have baseEven : base % 2 = 0 := by
        have baseTwice : base = 2 * (b * 2 ^ rest) := by
          simp [base, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
        rw [baseTwice]
        omega
      rw [valueBase]
      omega
    have rawShape : 9 * a - 1 = 8 * value + 2 := by
      omega
    rw [rawShape]
    exact R_eight_two_of_even valuePositive valueEven

def largeDiamondOtherChild
    (coefficient exponent tailBit : Nat) : Nat :=
  if exponent = 2 then
    A (Q coefficient (exponent - 1) (1 - tailBit))
  else
    B (Q coefficient (exponent - 1) (1 - tailBit))

/-- All valuation rows of the arithmetic large-diamond identity. -/
theorem largeDiamond_identity
    {a b exponent tailBit : Nat}
    (aPositive : 0 < a) (bPositive : 0 < b)
    (bOdd : OddNat b) (bit : Bit tailBit)
    (exponentLarge : 2 ≤ exponent)
    (valuation :
      3 * a + 1 - 2 * tailBit = 2 ^ exponent * b) :
    B (Q (3 * a) 1 tailBit) =
      largeDiamondOtherChild b exponent tailBit := by
  by_cases exponentTwo : exponent = 2
  · subst exponent
    simp only [largeDiamondOtherChild]
    simpa using largeDiamond_identity_valuation_two
      aPositive bPositive bOdd bit (by simpa using valuation)
  · by_cases exponentThree : exponent = 3
    · subst exponent
      simp only [largeDiamondOtherChild, if_neg (by omega)]
      simpa using largeDiamond_identity_valuation_three
        aPositive bPositive bOdd bit (by simpa using valuation)
    · have exponentHigh : 4 ≤ exponent := by omega
      simp only [largeDiamondOtherChild, if_neg exponentTwo]
      exact largeDiamond_identity_valuation_high
        aPositive bPositive bOdd bit exponentHigh valuation

/-- The adjacent valuation pair has the required common/other-child order. -/
theorem largeDiamond_adjacent_children
    {b exponent tailBit : Nat}
    (bPositive : 0 < b) (bOdd : OddNat b) (bit : Bit tailBit)
    (exponentLarge : 2 ≤ exponent) :
    let d := Q b exponent (1 - tailBit)
    let c := Q b (exponent - 1) (1 - tailBit)
    (A c = B d ∧
        B c = largeDiamondOtherChild b exponent tailBit) ∨
      (A c = largeDiamondOtherChild b exponent tailBit ∧
        B c = B d) := by
  dsimp only
  have complementBit : Bit (1 - tailBit) := by
    rcases bit with hzero | hone
    · right
      omega
    · left
      omega
  by_cases exponentTwo : exponent = 2
  · subst exponent
    right
    constructor
    · simp [largeDiamondOtherChild]
    · exact B_Q_one_eq_two bPositive bOdd complementBit
  · have exponentThree : 3 ≤ exponent := by omega
    left
    constructor
    · rw [A_Q bPositive complementBit (by omega)]
      rw [B_Q bPositive complementBit exponentThree]
      rw [show exponent - 1 - 1 = exponent - 2 by omega]
    · simp [largeDiamondOtherChild, exponentTwo]
/--
The outcome-theoretic core of Section 20.  Once the arithmetic identifies
`x` as a common child and `y` as both the other child of `c` and a child of
the DRAW state `k`, the advertised fingerprint is contradictory.
-/
theorem largeDiamond_outcome_contradiction
    {d c k x y : Nat}
    (dPositive : 0 < d) (dLosing : Losing d)
    (cWinning : Winning c) (kDraw : Draw k)
    (xChildOfD : x = A d ∨ x = B d)
    (childrenOfC :
      (A c = x ∧ B c = y) ∨ (A c = y ∧ B c = x))
    (yChildOfK : y = A k ∨ y = B k) : False := by
  have dChildren := dLosing.children_winning dPositive
  have xWinning : Winning x := by
    rcases xChildOfD with xIsA | xIsB
    · rw [xIsA]
      exact dChildren.1
    · rw [xIsB]
      exact dChildren.2
  have yLosing : Losing y := by
    rcases childrenOfC with cOrder | cOrder
    · have notLosingA : ¬ Losing (A c) := by
        rw [cOrder.1]
        exact xWinning.not_losing
      have losingB := cWinning.B_losing_of_A_not_losing notLosingA
      rwa [cOrder.2] at losingB
    · have notLosingB : ¬ Losing (B c) := by
        rw [cOrder.2]
        exact xWinning.not_losing
      have losingA := cWinning.A_losing_of_B_not_losing notLosingB
      rwa [cOrder.1] at losingA
  rcases yChildOfK with yIsA | yIsB
  · apply kDraw.children_not_losing.1
    rwa [← yIsA]
  · apply kDraw.children_not_losing.2
    rwa [← yIsB]

/--
Section 20 in assembled form: the exact valuation frame and the stated
LOSS/WIN/DRAW fingerprint are inconsistent for every valuation `>= 2`.
-/
theorem phaseMismatch_largeDiamond_contradiction
    {a b exponent tailBit : Nat}
    (aPositive : 0 < a) (bPositive : 0 < b)
    (bOdd : OddNat b) (bit : Bit tailBit)
    (exponentLarge : 2 ≤ exponent)
    (valuation :
      3 * a + 1 - 2 * tailBit = 2 ^ exponent * b)
    (dLosing : Losing (Q b exponent (1 - tailBit)))
    (cWinning : Winning (Q b (exponent - 1) (1 - tailBit)))
    (kDraw : Draw (Q (3 * a) 1 tailBit)) : False := by
  have complementBit : Bit (1 - tailBit) := by
    rcases bit with hzero | hone
    · right
      omega
    · left
      omega
  have dPositive : 0 < Q b exponent (1 - tailBit) :=
    IsConstantTail.state_positive
      ⟨bPositive, bOdd, by omega, complementBit, rfl⟩
  have adjacent := largeDiamond_adjacent_children
    bPositive bOdd bit exponentLarge
  have otherIdentity := largeDiamond_identity
    aPositive bPositive bOdd bit exponentLarge valuation
  exact largeDiamond_outcome_contradiction
    dPositive dLosing cWinning kDraw
    (Or.inr rfl) adjacent (Or.inr otherIdentity.symm)

/--
The Section 19 outcome fingerprint, isolated from the residue calculation.
Once the returned source `B(z)` is below the global minimum and an adjacent
exponent-one/two pair is attached to a DRAW parent, all three outcomes used by
the large diamond are forced.
-/
theorem minimumSource_nonselected_adjacent_fingerprint
    {source z parent : Nat}
    (minimum : MinimumDrawSource source)
    (returnedSourceDrops : B z < source)
    (parentDraw : Draw parent)
    (contractingChild :
      B parent = Q (embeddedValue z) 1
        (1 - sourceASelectingBit z))
    (expandingChild :
      A parent = Q (embeddedValue z) 2
        (1 - sourceASelectingBit z)) :
    let p := Q (embeddedValue z) 1 (1 - sourceASelectingBit z)
    let h := Q (embeddedValue z) 2 (1 - sourceASelectingBit z)
    Losing (A p) ∧ Winning (B p) ∧ Draw (A h) := by
  dsimp only
  let p := Q (embeddedValue z) 1 (1 - sourceASelectingBit z)
  let h := Q (embeddedValue z) 2 (1 - sourceASelectingBit z)
  have sourceA : StateHasSource (A p) (B z) := by
    simpa [p] using sourceLift_nonselected_hasSource z
  have sourceB : StateHasSource (B p) (B z) := by
    simpa [p] using sourceLift_nonselected_side_hasSource z
  have notDrawA : ¬ Draw (A p) :=
    minimum.not_draw_of_smaller sourceA returnedSourceDrops
  have notDrawB : ¬ Draw (B p) :=
    minimum.not_draw_of_smaller sourceB returnedSourceDrops
  have pNotDraw : ¬ Draw p := by
    intro pDraw
    obtain ⟨next, move, nextDraw⟩ := pDraw.has_draw_child
    rcases move.2 with nextA | nextB
    · subst next
      exact notDrawA nextDraw
    · subst next
      exact notDrawB nextDraw
  have pNotLosing : ¬ Losing p := by
    have childNotLosing := parentDraw.children_not_losing.2
    rw [contractingChild] at childNotLosing
    exact childNotLosing
  have pWinning : Winning p :=
    winning_of_not_draw_and_not_losing pNotDraw pNotLosing
  have hDraw : Draw h := by
    have drawA := parentDraw.A_of_B_winning (by
      rw [contractingChild]
      exact pWinning)
    rw [expandingChild] at drawA
    exact drawA
  have complementBit : Bit (1 - sourceASelectingBit z) := by
    have bit := sourceASelectingBit_is_bit z
    rcases bit with hzero | hone
    · right
      omega
    · left
      omega
  have commonChild : B h = B p := by
    exact (B_Q_one_eq_two (embeddedValue_positive z)
      (embeddedValue_odd z) complementBit).symm
  have commonNotLosing : ¬ Losing (B p) := by
    rw [← commonChild]
    exact hDraw.children_not_losing.2
  have commonWinning : Winning (B p) :=
    winning_of_not_draw_and_not_losing notDrawB commonNotLosing
  have dLosing : Losing (A p) :=
    pWinning.A_losing_of_B_not_losing commonNotLosing
  have kDraw : Draw (A h) := by
    apply hDraw.A_of_B_winning
    rw [commonChild]
    exact commonWinning
  exact ⟨dLosing, commonWinning, kDraw⟩

/--
Combined Sections 19--20 closure: a minimum-source DRAW parent cannot have
the displayed adjacent nonselected pair when its returned source drops below
the minimum.
-/
theorem minimumSource_nonselected_adjacent_impossible
    {source z parent : Nat}
    (minimum : MinimumDrawSource source)
    (returnedSourceDrops : B z < source)
    (parentDraw : Draw parent)
    (contractingChild :
      B parent = Q (embeddedValue z) 1
        (1 - sourceASelectingBit z))
    (expandingChild :
      A parent = Q (embeddedValue z) 2
        (1 - sourceASelectingBit z)) : False := by
  let tailBit := 1 - sourceASelectingBit z
  let p := Q (embeddedValue z) 1 tailBit
  let h := Q (embeddedValue z) 2 tailBit
  obtain ⟨exponent, exponentLarge, tail⟩ :=
    sourceLift_nonselected_constantTail z
  have selectingBit := sourceASelectingBit_is_bit z
  have bit : Bit tailBit := by
    dsimp [tailBit]
    rcases selectingBit with hzero | hone
    · right
      omega
    · left
      omega
  have fingerprint := minimumSource_nonselected_adjacent_fingerprint
    minimum returnedSourceDrops parentDraw contractingChild expandingChild
  have dEquation :
      A p = Q (embeddedValue (B z)) exponent (1 - tailBit) := by
    have complement : 1 - tailBit = sourceASelectingBit z := by
      dsimp [tailBit]
      rcases selectingBit with hzero | hone <;> omega
    simpa [p, tailBit, complement] using tail.equation
  have cEquation :
      B p = Q (embeddedValue (B z)) (exponent - 1) (1 - tailBit) := by
    unfold B
    rw [dEquation]
    exact R_Q tail.positive
      (by
        have complement : 1 - tailBit = sourceASelectingBit z := by
          dsimp [tailBit]
          rcases selectingBit with hzero | hone <;> omega
        simpa [complement] using sourceASelectingBit_is_bit z)
      exponentLarge
  have kEquation :
      A h = Q (3 * embeddedValue z) 1 tailBit := by
    dsimp [h]
    simpa using A_Q (embeddedValue_positive z) bit (by omega : 1 ≤ 2)
  have valuation :
      3 * embeddedValue z + 1 - 2 * tailBit =
        2 ^ exponent * embeddedValue (B z) := by
    have expanded : A p = Q (3 * embeddedValue z) 0 tailBit := by
      dsimp [p]
      simpa using A_Q (embeddedValue_positive z) bit (by omega : 1 ≤ 1)
    have equality := expanded.symm.trans dEquation
    have productPositive :
        0 < 2 ^ exponent * embeddedValue (B z) :=
      Nat.mul_pos (Nat.pow_pos (by omega)) (embeddedValue_positive (B z))
    rcases selectingBit with hzero | hone
    · dsimp [tailBit] at equality ⊢
      rw [hzero] at equality ⊢
      simp [Q, Nat.mul_comm] at equality ⊢
      omega
    · dsimp [tailBit] at equality ⊢
      rw [hone] at equality ⊢
      simp [Q, Nat.mul_comm] at equality ⊢
      omega
  have dLosing :
      Losing (Q (embeddedValue (B z)) exponent (1 - tailBit)) := by
    rw [← dEquation]
    simpa [p, h, tailBit] using fingerprint.1
  have cWinning :
      Winning
        (Q (embeddedValue (B z)) (exponent - 1) (1 - tailBit)) := by
    rw [← cEquation]
    simpa [p, h, tailBit] using fingerprint.2.1
  have kDraw : Draw (Q (3 * embeddedValue z) 1 tailBit) := by
    rw [← kEquation]
    simpa [p, h, tailBit] using fingerprint.2.2
  exact phaseMismatch_largeDiamond_contradiction
    (embeddedValue_positive z) (embeddedValue_positive (B z))
    (embeddedValue_odd (B z)) bit exponentLarge valuation
    dLosing cWinning kDraw

/-- A certified Section 19 mismatch frame is impossible at minimum source. -/
theorem minimumSource_mismatchFrame_impossible
    {source : Nat} (sourcePositive : 0 < source)
    (minimum : MinimumDrawSource source)
    (initialDraw :
      Draw (Q (embeddedValue source) 1 (sourceASelectingBit source)))
    (frame : MismatchAdjacentFrame source)
    (returnedSourceDrops : B (B (A source)) < source) : False := by
  have firstStep := minimumSource_sourceLift_forces_next
    sourcePositive minimum initialDraw
  have secondDraw :
      Draw
        (Q (embeddedValue (A source)) 1
          (1 - sourceASelectingBit source)) := firstStep.2
  dsimp [MismatchAdjacentFrame] at frame
  have contracting :
      B (Q (embeddedValue (A source)) 1
          (1 - sourceASelectingBit source)) =
        Q (embeddedValue (B (A source))) 1
          (1 - sourceASelectingBit (B (A source))) := by
    calc
      _ = Q (embeddedValue (B (A source))) 1
          (sourceASelectingBit source) := frame.2.1
      _ = _ := by rw [frame.1]
  have expanding :
      A (Q (embeddedValue (A source)) 1
          (1 - sourceASelectingBit source)) =
        Q (embeddedValue (B (A source))) 2
          (1 - sourceASelectingBit (B (A source))) := by
    calc
      _ = Q (embeddedValue (B (A source))) 2
          (sourceASelectingBit source) := frame.2.2
      _ = _ := by rw [frame.1]
  exact minimumSource_nonselected_adjacent_impossible
    minimum returnedSourceDrops secondDraw contracting expanding

theorem minimumSource_mismatch_five
    {t : Nat} (minimum : MinimumDrawSource (32 * t + 5)) :
    ¬ Draw
      (Q (embeddedValue (32 * t + 5)) 1
        (sourceASelectingBit (32 * t + 5))) := by
  intro initialDraw
  exact minimumSource_mismatchFrame_impossible (by omega) minimum initialDraw
    (mismatchAdjacentFrame_five t) (mismatchReturnedSourceDrop_five t)

theorem minimumSource_mismatch_fifteen
    {t : Nat} (minimum : MinimumDrawSource (32 * t + 15)) :
    ¬ Draw
      (Q (embeddedValue (32 * t + 15)) 1
        (sourceASelectingBit (32 * t + 15))) := by
  intro initialDraw
  exact minimumSource_mismatchFrame_impossible (by omega) minimum initialDraw
    (mismatchAdjacentFrame_fifteen t) (mismatchReturnedSourceDrop_fifteen t)

theorem minimumSource_mismatch_sixteen
    {t : Nat} (minimum : MinimumDrawSource (32 * t + 16)) :
    ¬ Draw
      (Q (embeddedValue (32 * t + 16)) 1
        (sourceASelectingBit (32 * t + 16))) := by
  intro initialDraw
  exact minimumSource_mismatchFrame_impossible (by omega) minimum initialDraw
    (mismatchAdjacentFrame_sixteen t) (mismatchReturnedSourceDrop_sixteen t)

theorem minimumSource_mismatch_twenty_six
    {t : Nat} (minimum : MinimumDrawSource (32 * t + 26)) :
    ¬ Draw
      (Q (embeddedValue (32 * t + 26)) 1
        (sourceASelectingBit (32 * t + 26))) := by
  intro initialDraw
  exact minimumSource_mismatchFrame_impossible (by omega) minimum initialDraw
    (mismatchAdjacentFrame_twenty_six t)
    (mismatchReturnedSourceDrop_twenty_six t)

end ThreeNPlusMinusOne
