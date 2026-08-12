import ThreeNPlusMinusOne.Certificate

set_option autoImplicit false

/-!
# A dependency-free proof-token multiset rank

The concrete proof inventory replaces one finite proof-height token by at
most two strictly lower descendants.  For this bounded split, the natural
number weight `3^height` is already sufficient: two terms of height at most
`h-1` weigh less than one term of height `h`.

Lists represent finite multisets only for purposes of the additive rank;
their order has no effect on `tokenRank`.  This avoids importing an ordinal
library while still kernel-checking the one-to-zero, one-to-one, and
one-to-two replacements actually used by the proof inventory.
-/

namespace ThreeNPlusMinusOne

def tokenWeight (height : Nat) : Nat :=
  3 ^ height

def tokenRank (tokens : List Nat) : Nat :=
  (tokens.map tokenWeight).sum

theorem three_pow_mono {lower upper : Nat} (h : lower ≤ upper) :
    3 ^ lower ≤ 3 ^ upper := by
  induction upper generalizing lower with
  | zero =>
      have : lower = 0 := by omega
      subst lower
      exact Nat.le_refl _
  | succ upper ih =>
      by_cases heq : lower = upper + 1
      · subst lower
        exact Nat.le_refl _
      · have hlower : lower ≤ upper := by omega
        have hprevious := ih hlower
        calc
          3 ^ lower ≤ 3 ^ upper := hprevious
          _ ≤ 3 ^ (upper + 1) := by
            rw [Nat.pow_succ]
            have hpositive : 0 < 3 ^ upper := Nat.pow_pos (by omega)
            omega

/-- A list of at most two lower heights weighs less than its parent. -/
theorem short_lower_tokenRank_lt
    {parent : Nat} {children : List Nat}
    (short : children.length ≤ 2)
    (lower : ∀ child ∈ children, child < parent) :
    tokenRank children < tokenWeight parent := by
  cases children with
  | nil =>
      simp [tokenRank, tokenWeight]
      exact Nat.pow_pos (by omega)
  | cons first tail =>
      cases tail with
      | nil =>
          have hfirst : first < parent := lower first (by simp)
          cases parent with
          | zero => omega
          | succ parent =>
              have hweight : 3 ^ first ≤ 3 ^ parent :=
                three_pow_mono (by omega)
              simp [tokenRank, tokenWeight, Nat.pow_succ]
              have hpositive : 0 < 3 ^ parent := Nat.pow_pos (by omega)
              omega
      | cons second rest =>
          cases rest with
          | nil =>
              have hfirst : first < parent := lower first (by simp)
              have hsecond : second < parent := lower second (by simp)
              cases parent with
              | zero => omega
              | succ parent =>
                  have hfirstWeight : 3 ^ first ≤ 3 ^ parent :=
                    three_pow_mono (by omega)
                  have hsecondWeight : 3 ^ second ≤ 3 ^ parent :=
                    three_pow_mono (by omega)
                  simp [tokenRank, tokenWeight, Nat.pow_succ]
                  have hpositive : 0 < 3 ^ parent := Nat.pow_pos (by omega)
                  omega
          | cons third rest =>
              simp at short

/--
Replace one occurrence of `parent` by zero, one, or two lower descendants.
The surrounding list is retained exactly.
-/
def TokenReplacement (next current : List Nat) : Prop :=
  ∃ before after parent children,
    current = before ++ parent :: after ∧
    next = before ++ children ++ after ∧
    children.length ≤ 2 ∧
    ∀ child ∈ children, child < parent

theorem tokenReplacement_decreases
    {next current : List Nat} (edge : TokenReplacement next current) :
    tokenRank next < tokenRank current := by
  obtain ⟨before, after, parent, children,
    rfl, rfl, short, lower⟩ := edge
  have hlocal := short_lower_tokenRank_lt short lower
  simp only [tokenRank, List.map_append, List.sum_append,
    List.map_cons, List.sum_cons]
  simp only [tokenRank] at hlocal
  omega

/-- The concrete bounded token-replacement relation is well-founded. -/
theorem tokenReplacement_wellFounded : WellFounded TokenReplacement := by
  apply Subrelation.wf
    (q := TokenReplacement)
    (r := InvImage Nat.lt tokenRank)
  · intro next current edge
    exact tokenReplacement_decreases edge
  · exact InvImage.wf tokenRank Nat.lt_wfRel.wf

end ThreeNPlusMinusOne
