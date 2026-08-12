import ThreeNPlusMinusOne.NormalForm

set_option autoImplicit false

/-!
# Exact conjugacy with the original signed game

This file closes the arithmetic bridge between the relational original moves
and the two maps `A` and `B`.  The proof is symbolic and unbounded.  Its key
recursive identity follows the same repeated-bit/alternating-bit split as the
definition of `R`.
-/

namespace ThreeNPlusMinusOne

theorem OddNat.not_even {n : Nat} (hodd : OddNat n) :
    ¬ ∃ k, n = 2 * k := by
  rintro ⟨k, hk⟩
  obtain ⟨j, hj⟩ := hodd
  omega

theorem RemoveTwos.self {x : Nat} (hodd : OddNat x) :
    RemoveTwos x x := by
  exact ⟨hodd, ⟨0, by simp⟩⟩

theorem even_or_odd (x : Nat) :
    (∃ k, x = 2 * k) ∨ OddNat x := by
  by_cases heven : x % 2 = 0
  · left
    exact ⟨x / 2, by omega⟩
  · right
    exact ⟨x / 2, by omega⟩

theorem RemoveTwos.double {x y : Nat} (h : RemoveTwos x y) :
    RemoveTwos (2 * x) y := by
  obtain ⟨hodd, k, hk⟩ := h
  refine ⟨hodd, k + 1, ?_⟩
  simp [hk, Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

/-- Removing one known factor of two does not change the odd part. -/
theorem RemoveTwos.of_double {x y : Nat} (h : RemoveTwos (2 * x) y) :
    RemoveTwos x y := by
  obtain ⟨odd, exponent, equation⟩ := h
  have exponentNonzero : exponent ≠ 0 := by
    intro exponentZero
    subst exponent
    simp only [Nat.pow_zero, Nat.one_mul] at equation
    exact odd.not_even ⟨x, equation.symm⟩
  obtain ⟨rest, exponentShape⟩ : ∃ rest, exponent = rest + 1 :=
    ⟨exponent - 1, by omega⟩
  subst exponent
  refine ⟨odd, rest, ?_⟩
  apply Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2)
  calc
    2 * x = 2 ^ (rest + 1) * y := equation
    _ = 2 * (2 ^ rest * y) := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

/-- Every positive natural number has an odd-part decomposition. -/
theorem RemoveTwos.exists_of_positive {x : Nat} (positive : 0 < x) :
    ∃ oddPart, RemoveTwos x oddPart := by
  refine Nat.strongRecOn
    (motive := fun x => 0 < x → ∃ oddPart, RemoveTwos x oddPart)
    x ?_ positive
  intro x ih positive
  rcases even_or_odd x with ⟨half, hhalf⟩ | hodd
  · have halfPositive : 0 < half := by omega
    have halfSmaller : half < x := by omega
    obtain ⟨oddPart, decomposition⟩ := ih half halfSmaller halfPositive
    refine ⟨oddPart, ?_⟩
    rw [hhalf]
    exact decomposition.double
  · exact ⟨x, RemoveTwos.self hodd⟩

private theorem odd_factor_forces_zero_exponent
    {oddValue factor exponent : Nat}
    (hodd : OddNat oddValue)
    (hfactor : oddValue = 2 ^ exponent * factor) :
    exponent = 0 := by
  by_cases hzero : exponent = 0
  · exact hzero
  · obtain ⟨d, hd⟩ : ∃ d, exponent = d + 1 := by
      exact ⟨exponent - 1, by omega⟩
    apply False.elim
    apply hodd.not_even
    refine ⟨2 ^ d * factor, ?_⟩
    rw [hfactor, hd, Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_left_comm]

/-- The relational removal of powers of two has a unique odd result. -/
theorem RemoveTwos.unique {x first second : Nat}
    (hfirst : RemoveTwos x first) (hsecond : RemoveTwos x second) :
    first = second := by
  obtain ⟨firstOdd, firstExponent, hfirstEq⟩ := hfirst
  obtain ⟨secondOdd, secondExponent, hsecondEq⟩ := hsecond
  rcases Nat.le_total firstExponent secondExponent with hle | hle
  · obtain ⟨difference, hdifference⟩ :
        ∃ difference, secondExponent = firstExponent + difference := by
      exact ⟨secondExponent - firstExponent, by omega⟩
    have hcancel : first = 2 ^ difference * second := by
      apply Nat.mul_left_cancel (n := 2 ^ firstExponent)
      · exact Nat.pow_pos (by omega)
      calc
        2 ^ firstExponent * first = x := hfirstEq.symm
        _ = 2 ^ secondExponent * second := hsecondEq
        _ = 2 ^ firstExponent * (2 ^ difference * second) := by
          simp [hdifference, Nat.pow_add, Nat.mul_assoc]
    have hzero := odd_factor_forces_zero_exponent firstOdd hcancel
    simpa [hzero] using hcancel
  · obtain ⟨difference, hdifference⟩ :
        ∃ difference, firstExponent = secondExponent + difference := by
      exact ⟨firstExponent - secondExponent, by omega⟩
    have hcancel : second = 2 ^ difference * first := by
      apply Nat.mul_left_cancel (n := 2 ^ secondExponent)
      · exact Nat.pow_pos (by omega)
      calc
        2 ^ secondExponent * second = x := hsecondEq.symm
        _ = 2 ^ firstExponent * first := hfirstEq
        _ = 2 ^ secondExponent * (2 ^ difference * first) := by
          simp [hdifference, Nat.pow_add, Nat.mul_assoc]
    have hzero := odd_factor_forces_zero_exponent secondOdd hcancel
    simpa [hzero] using hcancel.symm

/-- Odd state with ordinary `m`-coordinate `n = 2m+1`. -/
def coordinateState (m : Nat) : OriginalState :=
  ⟨2 * m + 1, by omega, ⟨m, rfl⟩⟩

/-- Original legal move expressed in ordinary `m`-coordinates. -/
def CoordinateMove (next current : Nat) : Prop :=
  OriginalMove (coordinateState current) (coordinateState next)

/-- The raw odd core which immediately yields `A(m)`. -/
def directCore (m : Nat) : Nat :=
  if m % 2 = 0 then 3 * m + 1 else 3 * m + 2

/-- The even raw core which recursively follows the alternating suffix. -/
def alternatingCore (m : Nat) : Nat :=
  if m % 2 = 0 then 3 * m + 2 else 3 * m + 1

theorem directCore_eq (m : Nat) : directCore m = 2 * A m + 1 := by
  simp only [directCore]
  split <;> unfold A <;> omega

theorem directCore_odd (m : Nat) : OddNat (directCore m) := by
  rw [directCore_eq]
  exact ⟨A m, rfl⟩

private theorem alternatingCore_boundary {m : Nat} (_hlarge : 2 ≤ m)
    (boundary : m % 2 = (m / 2) % 2) :
    alternatingCore m = 2 * (2 * A (m / 2) + 1) := by
  simp only [alternatingCore]
  split <;> unfold A <;> omega

private theorem alternatingCore_scan {m : Nat} (_hlarge : 2 ≤ m)
    (alternates : m % 2 ≠ (m / 2) % 2) :
    alternatingCore m = 2 * alternatingCore (m / 2) := by
  simp only [alternatingCore]
  split <;> split <;> omega

/-- The alternating raw core normalizes exactly to `2*A(R(m))+1`. -/
theorem alternatingCore_removeTwos (m : Nat) :
    RemoveTwos (alternatingCore m) (2 * A (R m) + 1) := by
  refine Nat.strongRecOn
    (motive := fun m =>
      RemoveTwos (alternatingCore m) (2 * A (R m) + 1)) m ?_
  intro m ih
  by_cases hzero : m = 0
  · subst m
    exact ⟨⟨0, by simp [A]⟩, ⟨1, by simp [alternatingCore, A]⟩⟩
  · by_cases hone : m = 1
    · subst m
      exact ⟨⟨0, by simp [A]⟩, ⟨2, by simp [alternatingCore, A]⟩⟩
    · have hlarge : 2 ≤ m := by omega
      by_cases boundary : m % 2 = (m / 2) % 2
      · rw [R_of_boundary hlarge boundary]
        rw [alternatingCore_boundary hlarge boundary]
        exact RemoveTwos.double (RemoveTwos.self ⟨A (m / 2), rfl⟩)
      · rw [R_of_alternates hlarge boundary]
        rw [alternatingCore_scan hlarge boundary]
        apply RemoveTwos.double
        apply ih
        exact Nat.div_lt_self (by omega) (by omega)

private theorem raw_direct {m : Nat} (hm : 0 < m) :
    ∃ sign, rawMove sign (coordinateState m).value = 2 * directCore m := by
  by_cases heven : m % 2 = 0
  · exact ⟨Sign.minus, by simp [rawMove, coordinateState, directCore, heven]; omega⟩
  · exact ⟨Sign.plus, by simp [rawMove, coordinateState, directCore, heven]; omega⟩

private theorem raw_alternating {m : Nat} (hm : 0 < m) :
    ∃ sign, rawMove sign (coordinateState m).value = 2 * alternatingCore m := by
  by_cases heven : m % 2 = 0
  · exact ⟨Sign.plus, by simp [rawMove, coordinateState, alternatingCore, heven]; omega⟩
  · exact ⟨Sign.minus, by simp [rawMove, coordinateState, alternatingCore, heven]; omega⟩

/-- The expanding normal-form child is an actual original signed move. -/
theorem coordinateMove_A {m : Nat} (hm : 0 < m) :
    CoordinateMove (A m) m := by
  refine ⟨by simp [coordinateState]; omega, ?_⟩
  obtain ⟨sign, hraw⟩ := raw_direct hm
  refine ⟨sign, ?_⟩
  rw [hraw, directCore_eq]
  exact RemoveTwos.double (RemoveTwos.self ⟨A m, rfl⟩)

/-- The contracting normal-form child is an actual original signed move. -/
theorem coordinateMove_R {m : Nat} (hm : 0 < m) :
    CoordinateMove (A (R m)) m := by
  refine ⟨by simp [coordinateState]; omega, ?_⟩
  obtain ⟨sign, hraw⟩ := raw_alternating hm
  refine ⟨sign, ?_⟩
  rw [hraw]
  exact RemoveTwos.double (alternatingCore_removeTwos m)

private theorem signed_raw_is_direct_or_alternating
    {m : Nat} (hm : 0 < m) (sign : Sign) :
    rawMove sign (coordinateState m).value = 2 * directCore m ∨
    rawMove sign (coordinateState m).value = 2 * alternatingCore m := by
  cases sign <;> simp only [rawMove, coordinateState]
  · by_cases heven : m % 2 = 0
    · left; simp [directCore, heven]; omega
    · right; simp [alternatingCore, heven]; omega
  · by_cases heven : m % 2 = 0
    · right; simp [alternatingCore, heven]; omega
    · left; simp [directCore, heven]; omega

/-- Exact unbounded two-child normal form in ordinary `m`-coordinates. -/
theorem coordinateMove_iff {next m : Nat} (hm : 0 < m) :
    CoordinateMove next m ↔ next = A m ∨ next = A (R m) := by
  constructor
  · rintro ⟨_, sign, hremove⟩
    rcases signed_raw_is_direct_or_alternating hm sign with hdirect | halternating
    · have expected : RemoveTwos
          (rawMove sign (coordinateState m).value) (2 * A m + 1) := by
        rw [hdirect, directCore_eq]
        exact RemoveTwos.double (RemoveTwos.self ⟨A m, rfl⟩)
      have hvalue := RemoveTwos.unique hremove expected
      left
      simp only [coordinateState] at hvalue
      omega
    · have expected : RemoveTwos
          (rawMove sign (coordinateState m).value) (2 * A (R m) + 1) := by
        rw [halternating]
        exact RemoveTwos.double (alternatingCore_removeTwos m)
      have hvalue := RemoveTwos.unique hremove expected
      right
      simp only [coordinateState] at hvalue
      omega
  · rintro (rfl | rfl)
    · exact coordinateMove_A hm
    · exact coordinateMove_R hm

theorem embed_eq_coordinateState (q : Nat) :
    embed q = coordinateState (A q) := by
  rfl

theorem OriginalState.eq_of_value_eq {first second : OriginalState}
    (hvalue : first.value = second.value) : first = second := by
  cases first with
  | mk firstValue firstPositive firstOdd =>
      cases second with
      | mk secondValue secondPositive secondOdd =>
          simp only at hvalue
          subst secondValue
          rfl

/--
Exact conjugacy theorem: the legal original children of `embed q` are
precisely `embed (A q)` and `embed (B q)`.
-/
theorem originalMove_embed_iff {q : Nat} (hq : 0 < q)
    (next : OriginalState) :
    OriginalMove (embed q) next ↔
      next = embed (A q) ∨ next = embed (B q) := by
  obtain ⟨nextCoordinate, hnextValue⟩ := next.odd
  have hnext : next = coordinateState nextCoordinate := by
    apply OriginalState.eq_of_value_eq
    exact hnextValue
  rw [hnext, embed_eq_coordinateState]
  have hApos : 0 < A q := A_pos hq
  change CoordinateMove nextCoordinate (A q) ↔
    coordinateState nextCoordinate = embed (A q) ∨
      coordinateState nextCoordinate = embed (B q)
  rw [coordinateMove_iff hApos]
  constructor
  · rintro (h | h)
    · left
      subst nextCoordinate
      rw [embed_eq_coordinateState]
    · right
      subst nextCoordinate
      rw [embed_eq_coordinateState]
      rfl
  · rintro (h | h)
    · left
      rw [embed_eq_coordinateState] at h
      have hvalue := congrArg OriginalState.value h
      simp only [coordinateState] at hvalue
      omega
    · right
      rw [embed_eq_coordinateState] at h
      have hvalue := congrArg OriginalState.value h
      simp only [coordinateState] at hvalue
      unfold B at hvalue
      omega

end ThreeNPlusMinusOne
