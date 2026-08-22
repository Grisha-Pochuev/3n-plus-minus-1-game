import ThreeNPlusMinusOne.OccurrenceRefinement
import ThreeNPlusMinusOne.OccurrenceCertificates

set_option autoImplicit false

/-!
# Data-level occurrence refinement boundary

This is the branch-choice-preserving counterpart of `OccurrenceRefinement`.
It carries `CertifiedProofForest`s, whose finite WIN/LOSS trees are data, and
erases every certified step into the already checked logical occurrence step.
The semantic `lift` and `progress` obligations remain explicit: this file
does not manufacture a global no-DRAW refinement.
-/

namespace ThreeNPlusMinusOne

structure CertifiedOccurrenceMacroConfiguration where
  base : MacroConfiguration
  outerForest : CertifiedProofForest
  innerForest : CertifiedProofForest

def certifiedOccurrenceForestRank
    (configuration : CertifiedOccurrenceMacroConfiguration) : Nat :=
  certifiedProofTokenRank configuration.outerForest +
    certifiedProofTokenRank configuration.innerForest

inductive CertifiedOccurrenceMacroStep :
    CertifiedOccurrenceMacroConfiguration →
      CertifiedOccurrenceMacroConfiguration → Prop
  | certified {next current : CertifiedOccurrenceMacroConfiguration}
      (edge : CertifiedMacroStep next.base current.base) :
      CertifiedOccurrenceMacroStep next current
  | outerForest {next current : CertifiedOccurrenceMacroConfiguration}
      (base : next.base = current.base)
      (inner : next.innerForest = current.innerForest)
      (edge : CertifiedProofTokenReplacement next.outerForest current.outerForest) :
      CertifiedOccurrenceMacroStep next current
  | innerForest {next current : CertifiedOccurrenceMacroConfiguration}
      (base : next.base = current.base)
      (outer : next.outerForest = current.outerForest)
      (edge : CertifiedProofTokenReplacement next.innerForest current.innerForest) :
      CertifiedOccurrenceMacroStep next current

def certifiedOccurrenceRank
    (configuration : CertifiedOccurrenceMacroConfiguration) :
    MacroConfiguration × Nat :=
  (configuration.base, certifiedOccurrenceForestRank configuration)

theorem certifiedOccurrenceMacroStep_decreases
    {next current : CertifiedOccurrenceMacroConfiguration}
    (edge : CertifiedOccurrenceMacroStep next current) :
    Prod.Lex CertifiedMacroStep Nat.lt
      (certifiedOccurrenceRank next) (certifiedOccurrenceRank current) := by
  cases edge with
  | certified edge =>
      apply Prod.Lex.left
      exact edge
  | outerForest base inner edge =>
      rw [certifiedOccurrenceRank, certifiedOccurrenceRank, base]
      apply Prod.Lex.right
      unfold certifiedOccurrenceForestRank
      rw [inner]
      exact Nat.add_lt_add_right
        (certifiedProofTokenReplacement_decreases edge) _
  | innerForest base outer edge =>
      rw [certifiedOccurrenceRank, certifiedOccurrenceRank, base]
      apply Prod.Lex.right
      unfold certifiedOccurrenceForestRank
      rw [outer]
      exact Nat.add_lt_add_left
        (certifiedProofTokenReplacement_decreases edge) _

theorem certifiedOccurrenceMacroStep_wellFounded :
    WellFounded CertifiedOccurrenceMacroStep := by
  exact rankedRelation_wellFounded certifiedOccurrenceRank
    certifiedMacroStep_wellFounded Nat.lt_wfRel.wf
    certifiedOccurrenceMacroStep_decreases

namespace CertifiedOccurrenceMacroConfiguration

/-- Forget retained branch choices, producing the existing logical occurrence
configuration. -/
def erase (configuration : CertifiedOccurrenceMacroConfiguration) :
    OccurrenceMacroConfiguration :=
  { base := configuration.base
    outerForest := configuration.outerForest.toProofForest
    innerForest := configuration.innerForest.toProofForest }

theorem erase_rank (configuration : CertifiedOccurrenceMacroConfiguration) :
    occurrenceRank configuration.erase = certifiedOccurrenceRank configuration := by
  unfold occurrenceRank certifiedOccurrenceRank
  unfold erase occurrenceForestRank certifiedOccurrenceForestRank
  rw [certifiedProofTokenRank_toProofForest,
    certifiedProofTokenRank_toProofForest]

end CertifiedOccurrenceMacroConfiguration

/-- Every data-level macro transition erases to a permitted logical
occurrence-level macro transition. -/
theorem CertifiedOccurrenceMacroStep.erase
    {next current : CertifiedOccurrenceMacroConfiguration}
    (edge : CertifiedOccurrenceMacroStep next current) :
    OccurrenceMacroStep next.erase current.erase := by
  cases edge with
  | certified edge =>
      exact OccurrenceMacroStep.certified edge
  | outerForest base inner edge =>
      exact OccurrenceMacroStep.outerForest base
        (congrArg CertifiedProofForest.toProofForest inner)
        (certifiedProofTokenReplacement_toProofTokenReplacement edge)
  | innerForest base outer edge =>
      exact OccurrenceMacroStep.innerForest base
        (congrArg CertifiedProofForest.toProofForest outer)
        (certifiedProofTokenReplacement_toProofTokenReplacement edge)

/-- A semantic refinement over data-level occurrence configurations. The
certificate carrier prevents a later route choice from replacing a stored
branch by an unrelated finite proof witness. -/
structure CertifiedOccurrenceDrawMacroRefinement where
  Bad : CertifiedOccurrenceMacroConfiguration → Prop
  lift : ∀ q, Draw q → ∃ configuration, Bad configuration
  progress : ∀ current, Bad current →
    ∃ next, CertifiedOccurrenceMacroStep next current ∧ Bad next

theorem CertifiedOccurrenceDrawMacroRefinement.no_draw
    (refinement : CertifiedOccurrenceDrawMacroRefinement) :
    ∀ q, ¬ Draw q := by
  exact no_draw_of_wellFounded_macro
    certifiedOccurrenceMacroStep_wellFounded
    refinement.Bad refinement.lift refinement.progress

end ThreeNPlusMinusOne
