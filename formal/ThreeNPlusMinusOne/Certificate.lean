set_option autoImplicit false

/-!
# Soundness kernel for a routing certificate

This file formalizes only the order-theoretic metatheorem used by the JSON
certificate.  It is deliberately independent of the game arithmetic.

If a concrete transition relation maps every step to a decrease in a
lexicographic pair of well-founded ranks, then the transition relation is
well-founded and admits no infinite descending chain.  The Python checker
adds a finite acyclic control rank after the four mathematical components;
repeated application of this theorem gives the same nested-fibre assembly.

This does not prove that the JSON macro rules cover the game.  That refinement
obligation remains in the explicit trust boundary.
-/

namespace ThreeNPlusMinusOne

universe u v w

/-- The lexicographic product of two well-founded relations is well-founded. -/
theorem lexPair_wellFounded
    {Outer : Type u} {Inner : Type v}
    {outerLt : Outer → Outer → Prop} {innerLt : Inner → Inner → Prop}
    (outerWf : WellFounded outerLt) (innerWf : WellFounded innerLt) :
    WellFounded (Prod.Lex outerLt innerLt) :=
  ⟨fun (outer, inner) =>
    Prod.lexAccessible
      (WellFounded.apply outerWf outer)
      (fun value => WellFounded.apply innerWf value)
      inner⟩

/-- Pulling a well-founded lexicographic rank back along `rank` is sound. -/
theorem rankedRelation_wellFounded
    {Configuration : Type w} {Outer : Type u} {Inner : Type v}
    {step : Configuration → Configuration → Prop}
    {outerLt : Outer → Outer → Prop} {innerLt : Inner → Inner → Prop}
    (rank : Configuration → Outer × Inner)
    (outerWf : WellFounded outerLt) (innerWf : WellFounded innerLt)
    (decreases : ∀ {next current}, step next current →
      Prod.Lex outerLt innerLt (rank next) (rank current)) :
    WellFounded step := by
  apply Subrelation.wf
    (q := step)
    (r := InvImage (Prod.Lex outerLt innerLt) rank)
  · intro next current edge
    exact decreases edge
  · exact InvImage.wf rank (lexPair_wellFounded outerWf innerWf)

/-- A concrete representation of an infinite descent. -/
def InfiniteDescending
    {Configuration : Type u}
    (step : Configuration → Configuration → Prop)
    (path : Nat → Configuration) : Prop :=
  ∀ n, step (path (n + 1)) (path n)

/-- Accessibility at the first node excludes an infinite descending path. -/
theorem Acc.noInfiniteDescending
    {Configuration : Type u} {step : Configuration → Configuration → Prop}
    {start : Configuration} (accessible : Acc step start) :
    ∀ path : Nat → Configuration,
      path 0 = start → ¬ InfiniteDescending step path := by
  induction accessible with
  | intro current predecessors inductionHypothesis =>
      intro path begins chain
      have firstEdge : step (path 1) current := by
        simpa [begins] using chain 0
      have tailImpossible := inductionHypothesis (path 1) firstEdge
        (fun n => path (n + 1)) rfl
      apply tailImpossible
      intro n
      simpa [Nat.add_assoc] using chain (n + 1)

/-- A well-founded certified relation admits no infinite descending path. -/
theorem wellFounded_noInfiniteDescending
    {Configuration : Type u} {step : Configuration → Configuration → Prop}
    (stepWf : WellFounded step) (path : Nat → Configuration) :
    ¬ InfiniteDescending step path := by
  exact Acc.noInfiniteDescending (WellFounded.apply stepWf (path 0)) path rfl

/--
The certificate soundness statement in its final user-facing form: two
well-founded rank components plus a checked decrease exclude an infinite
macro route.
-/
theorem acceptedCertificate_excludesInfiniteRoute
    {Configuration : Type w} {Outer : Type u} {Inner : Type v}
    {step : Configuration → Configuration → Prop}
    {outerLt : Outer → Outer → Prop} {innerLt : Inner → Inner → Prop}
    (rank : Configuration → Outer × Inner)
    (outerWf : WellFounded outerLt) (innerWf : WellFounded innerLt)
    (decreases : ∀ {next current}, step next current →
      Prod.Lex outerLt innerLt (rank next) (rank current))
    (path : Nat → Configuration) :
    ¬ InfiniteDescending step path := by
  apply wellFounded_noInfiniteDescending
  exact rankedRelation_wellFounded rank outerWf innerWf decreases

end ThreeNPlusMinusOne
