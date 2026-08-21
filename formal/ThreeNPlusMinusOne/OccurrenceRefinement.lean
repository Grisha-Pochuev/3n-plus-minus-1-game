import ThreeNPlusMinusOne.MacroCertificate
import ThreeNPlusMinusOne.TokenProvenance
import ThreeNPlusMinusOne.Outcome

set_option autoImplicit false

/-!
# The occurrence-level refinement boundary

`MacroConfiguration` records only numerical token heights.  The missing
global theorem needs the stronger object in which the actual finite proof
occurrences are carried as well.  This file gives that object and its
well-founded transition relation.  A macro transition may rebuild the forest
only after a strict certified macro decrease; at equal macro rank, the only
allowed changes are exact lower-occurrence replacements.

The semantic `lift` and `progress` fields below are intentionally still a
premise.  They are the precise no-reseed obligations that a concrete game
refinement must discharge.
-/

namespace ThreeNPlusMinusOne

structure OccurrenceMacroConfiguration where
  base : MacroConfiguration
  outerForest : ProofForest
  innerForest : ProofForest

def occurrenceForestRank (configuration : OccurrenceMacroConfiguration) : Nat :=
  proofTokenRank configuration.outerForest +
    proofTokenRank configuration.innerForest

inductive OccurrenceMacroStep :
    OccurrenceMacroConfiguration → OccurrenceMacroConfiguration → Prop
  | certified {next current : OccurrenceMacroConfiguration}
      (edge : CertifiedMacroStep next.base current.base) :
      OccurrenceMacroStep next current
  | outerForest {next current : OccurrenceMacroConfiguration}
      (base : next.base = current.base)
      (inner : next.innerForest = current.innerForest)
      (edge : ProofTokenReplacement next.outerForest current.outerForest) :
      OccurrenceMacroStep next current
  | innerForest {next current : OccurrenceMacroConfiguration}
      (base : next.base = current.base)
      (outer : next.outerForest = current.outerForest)
      (edge : ProofTokenReplacement next.innerForest current.innerForest) :
      OccurrenceMacroStep next current

def occurrenceRank (configuration : OccurrenceMacroConfiguration) :
    MacroConfiguration × Nat :=
  (configuration.base, occurrenceForestRank configuration)

theorem occurrenceMacroStep_decreases
    {next current : OccurrenceMacroConfiguration}
    (edge : OccurrenceMacroStep next current) :
    Prod.Lex CertifiedMacroStep Nat.lt
      (occurrenceRank next) (occurrenceRank current) := by
  cases edge with
  | certified edge =>
      apply Prod.Lex.left
      exact edge
  | outerForest base inner edge =>
      rw [occurrenceRank, occurrenceRank, base]
      apply Prod.Lex.right
      unfold occurrenceForestRank
      rw [inner]
      exact Nat.add_lt_add_right (proofTokenReplacement_decreases edge) _
  | innerForest base outer edge =>
      rw [occurrenceRank, occurrenceRank, base]
      apply Prod.Lex.right
      unfold occurrenceForestRank
      rw [outer]
      exact Nat.add_lt_add_left (proofTokenReplacement_decreases edge) _

theorem occurrenceMacroStep_wellFounded :
    WellFounded OccurrenceMacroStep := by
  exact rankedRelation_wellFounded occurrenceRank
    certifiedMacroStep_wellFounded Nat.lt_wfRel.wf
    occurrenceMacroStep_decreases

/-- A semantic refinement over exact occurrence-carrying macro states. -/
structure OccurrenceDrawMacroRefinement where
  Bad : OccurrenceMacroConfiguration → Prop
  lift : ∀ q, Draw q → ∃ configuration, Bad configuration
  progress : ∀ current, Bad current →
    ∃ next, OccurrenceMacroStep next current ∧ Bad next

theorem OccurrenceDrawMacroRefinement.no_draw
    (refinement : OccurrenceDrawMacroRefinement) :
    ∀ q, ¬ Draw q := by
  exact no_draw_of_wellFounded_macro
    occurrenceMacroStep_wellFounded
    refinement.Bad refinement.lift refinement.progress

end ThreeNPlusMinusOne
