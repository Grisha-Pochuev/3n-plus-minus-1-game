import ThreeNPlusMinusOne.MacroCertificate
import ThreeNPlusMinusOne.Outcome

set_option autoImplicit false

/-!
# Explicit semantic refinement boundary

The rank assembly and the game-theoretic no-DRAW principle are both proved.
What remains is the concrete refinement connecting them.  Packaging that
refinement as data prevents an assembly theorem from silently assuming any
of its semantic obligations.
-/

namespace ThreeNPlusMinusOne

/--
A complete refinement of the human macro inventory must provide:

* an initial bad macro configuration for every conjugated DRAW state; and
* a productive certified macro successor for every bad configuration.

The second field is where arithmetic guard coverage, outcome-compatible DRAW
selection, and finite productivity of each normalization macro meet.
-/
structure DrawMacroRefinement where
  Bad : MacroConfiguration → Prop
  lift : ∀ q, Draw q → ∃ configuration, Bad configuration
  progress : ∀ current, Bad current →
    ∃ next, CertifiedMacroStep next current ∧ Bad next

/-- A complete concrete macro refinement rules out every DRAW state. -/
theorem DrawMacroRefinement.no_draw (refinement : DrawMacroRefinement) :
    ∀ q, ¬ Draw q := by
  exact no_draw_of_wellFounded_macro
    certifiedMacroStep_wellFounded
    refinement.Bad refinement.lift refinement.progress

/-- A complete concrete macro refinement resolves every conjugated state. -/
theorem DrawMacroRefinement.resolved (refinement : DrawMacroRefinement) :
    ∀ q, Resolved q := by
  intro q
  exact (not_draw_iff_resolved q).mp (refinement.no_draw q)

end ThreeNPlusMinusOne
