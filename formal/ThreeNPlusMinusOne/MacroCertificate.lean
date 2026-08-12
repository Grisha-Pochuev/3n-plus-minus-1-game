import ThreeNPlusMinusOne.TokenRank
import ThreeNPlusMinusOne.Certificate

set_option autoImplicit false

/-!
# Kernel-checked rank assembly for the macro control graph

The JSON certificate has four mathematical rank components followed by a
finite control DAG on the transitions which preserve all four components.
This file mirrors that order in Lean.  It proves the resulting abstract macro
relation well-founded; it does not assert that every game continuation is one
of these macro steps.  That semantic refinement remains an explicit separate
obligation.
-/

namespace ThreeNPlusMinusOne

inductive ControlState
  | minimumSourceEntry
  | heightOneEntry
  | aObligation
  | aTest4
  | aTest3
  | aTest2
  | aTest1
  | bSelect
  | b2First
  | b2Ready
  | factorFork
  | highReturn
  | markedTail
  | shortExactLift
  | terminalMacro
  deriving DecidableEq, Repr

/-- The 16 equal-rank JSON transitions. -/
inductive EqualControlStep : ControlState → ControlState → Prop
  | minimumToObligation : EqualControlStep .aObligation .minimumSourceEntry
  | heightToObligation : EqualControlStep .aObligation .heightOneEntry
  | obligationToA4 : EqualControlStep .aTest4 .aObligation
  | obligationToFactor : EqualControlStep .factorFork .aObligation
  | a4ToA3 : EqualControlStep .aTest3 .aTest4
  | a4ToB : EqualControlStep .bSelect .aTest4
  | a3ToA2 : EqualControlStep .aTest2 .aTest3
  | a3ToB : EqualControlStep .bSelect .aTest3
  | a2ToA1 : EqualControlStep .aTest1 .aTest2
  | a2ToB : EqualControlStep .bSelect .aTest2
  | a1ToB : EqualControlStep .bSelect .aTest1
  | bToFirst : EqualControlStep .b2First .bSelect
  | firstToReady : EqualControlStep .b2Ready .b2First
  | factorToHigh : EqualControlStep .highReturn .factorFork
  | markedD2ToShort : EqualControlStep .shortExactLift .markedTail
  | shortToObligation : EqualControlStep .aObligation .shortExactLift

/-- A topological height for the equal-rank control graph. -/
def controlRank : ControlState → Nat
  | .minimumSourceEntry => 8
  | .heightOneEntry => 8
  | .aObligation => 7
  | .aTest4 => 6
  | .aTest3 => 5
  | .aTest2 => 4
  | .aTest1 => 3
  | .bSelect => 2
  | .b2First => 1
  | .b2Ready => 0
  | .factorFork => 1
  | .highReturn => 0
  | .markedTail => 9
  | .shortExactLift => 8
  | .terminalMacro => 0

theorem equalControlStep_decreases
    {next current : ControlState} (edge : EqualControlStep next current) :
    controlRank next < controlRank current := by
  cases edge <;> decide

theorem equalControlStep_wellFounded : WellFounded EqualControlStep := by
  apply Subrelation.wf
    (q := EqualControlStep)
    (r := InvImage Nat.lt controlRank)
  · intro next current edge
    exact equalControlStep_decreases edge
  · exact InvImage.wf controlRank Nat.lt_wfRel.wf

/-- Data carried by the four-component global certificate plus control. -/
structure MacroConfiguration where
  outerSource : Nat
  outerTokens : List Nat
  innerSource : Nat
  innerTokens : List Nat
  control : ControlState

/--
Abstract size-change relation accepted by the certificate: the first changed
component strictly decreases, or all four components are retained and the
finite control state advances in its DAG.
-/
inductive CertifiedMacroStep : MacroConfiguration → MacroConfiguration → Prop
  | outerSource {next current : MacroConfiguration}
      (decrease : next.outerSource < current.outerSource) :
      CertifiedMacroStep next current
  | outerTokens {next current : MacroConfiguration}
      (source : next.outerSource = current.outerSource)
      (decrease : tokenRank next.outerTokens < tokenRank current.outerTokens) :
      CertifiedMacroStep next current
  | innerSource {next current : MacroConfiguration}
      (outerSource : next.outerSource = current.outerSource)
      (outerTokens : tokenRank next.outerTokens = tokenRank current.outerTokens)
      (decrease : next.innerSource < current.innerSource) :
      CertifiedMacroStep next current
  | innerTokens {next current : MacroConfiguration}
      (outerSource : next.outerSource = current.outerSource)
      (outerTokens : tokenRank next.outerTokens = tokenRank current.outerTokens)
      (innerSource : next.innerSource = current.innerSource)
      (decrease : tokenRank next.innerTokens < tokenRank current.innerTokens) :
      CertifiedMacroStep next current
  | control {next current : MacroConfiguration}
      (outerSource : next.outerSource = current.outerSource)
      (outerTokens : tokenRank next.outerTokens = tokenRank current.outerTokens)
      (innerSource : next.innerSource = current.innerSource)
      (innerTokens : tokenRank next.innerTokens = tokenRank current.innerTokens)
      (advance : EqualControlStep next.control current.control) :
      CertifiedMacroStep next current

abbrev InnerRank := Nat × (Nat × (Nat × Nat))

def innerRank (configuration : MacroConfiguration) : InnerRank :=
  (tokenRank configuration.outerTokens,
    configuration.innerSource,
    tokenRank configuration.innerTokens,
    controlRank configuration.control)

def certifiedRank (configuration : MacroConfiguration) : Nat × InnerRank :=
  (configuration.outerSource, innerRank configuration)

abbrev InnerRankLt : InnerRank → InnerRank → Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))

theorem innerRankLt_wellFounded : WellFounded InnerRankLt := by
  exact lexPair_wellFounded Nat.lt_wfRel.wf
    (lexPair_wellFounded Nat.lt_wfRel.wf
      (lexPair_wellFounded Nat.lt_wfRel.wf Nat.lt_wfRel.wf))

theorem certifiedMacroStep_decreases
    {next current : MacroConfiguration}
    (edge : CertifiedMacroStep next current) :
    Prod.Lex Nat.lt InnerRankLt
      (certifiedRank next) (certifiedRank current) := by
  cases edge with
  | outerSource decrease =>
      apply Prod.Lex.left
      exact decrease
  | outerTokens source decrease =>
      rw [certifiedRank, certifiedRank, source]
      apply Prod.Lex.right
      apply Prod.Lex.left
      exact decrease
  | innerSource outerSource outerTokens decrease =>
      rw [certifiedRank, certifiedRank, outerSource]
      apply Prod.Lex.right
      rw [innerRank, innerRank, outerTokens]
      apply Prod.Lex.right
      apply Prod.Lex.left
      exact decrease
  | innerTokens outerSource outerTokens innerSource decrease =>
      rw [certifiedRank, certifiedRank, outerSource]
      apply Prod.Lex.right
      rw [innerRank, innerRank, outerTokens, innerSource]
      apply Prod.Lex.right
      apply Prod.Lex.right
      apply Prod.Lex.left
      exact decrease
  | control outerSource outerTokens innerSource innerTokens advance =>
      rw [certifiedRank, certifiedRank, outerSource]
      apply Prod.Lex.right
      rw [innerRank, innerRank, outerTokens, innerSource, innerTokens]
      apply Prod.Lex.right
      apply Prod.Lex.right
      apply Prod.Lex.right
      exact equalControlStep_decreases advance

/-- The four-component size-change certificate plus control DAG is sound. -/
theorem certifiedMacroStep_wellFounded : WellFounded CertifiedMacroStep := by
  exact rankedRelation_wellFounded certifiedRank
    Nat.lt_wfRel.wf innerRankLt_wellFounded
    certifiedMacroStep_decreases

end ThreeNPlusMinusOne
