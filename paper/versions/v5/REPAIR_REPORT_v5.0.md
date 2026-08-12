# Repair report: v4.0 -> v5.0

## Executive result

Version 5.0 does not attempt to make the v4.0 global proof look complete by adding another ranking component. Instead it removes the two unjustified global steps from the theorem claim, keeps the local mathematics that survives audit, turns the known counterexamples into permanent regression tests, and states the exact remaining mathematical obligations.

## 1. Multi-A retained-anchor bug — repaired by removing the inference

The v4.0 route effectively needed a comparison of a returned B-source with an older retained source. The explicit trajectory

`20 -> 30 -> 45 -> 68`, `B(68)=25`

shows that the comparison can fail: 25 is larger than the retained 20.

In v5.0:

- all A-streak ordinary sources are temporary cursors;
- `b_select -> factor_fork` at valuation >= 3 is pure routing, not a source decrease;
- no later source may replace the retained anchor without an exact source certificate;
- valuation-two upward reset is `OPEN-P1`.

## 2. Semantic-completeness bug — made explicit as P2

The v4.0 finite control graph was not enough to establish that every actual DRAW path satisfied one of its declared rows.

In v5.0:

- the graph is explicitly a bookkeeping object;
- each open reset is visibly labelled `OPEN-P2`;
- P2 specifies the exact semantic table required before the graph can be promoted to a theorem;
- finite endpoints of unrelated proof height are forbidden from entering the ranked token multiset.

## 3. Valuation-two recycle — no longer hand-waved

The v4.0 text did not fully justify a strict proof-token comparison across a general multi-A streak followed by a valuation-two return.

In v5.0 this is not declared solved. P1 gives the acceptance criteria for a valid proof and explicitly includes all exceptional residue classes.

## 4. LOSS/non-DRAW side cases — included in the semantic obligation

Any outcome split that produces a finite LOSS or WIN state must give the exact parent/child incidence needed for its use. A finite outcome by itself is not a token comparison. P2 makes this a row-by-row requirement.

## 5. Machine-check scope — hardened

The verifier now performs four distinct jobs:

1. positive arithmetic identity checks;
2. the two negative regressions that must remain counterexamples;
3. acyclicity of the **pure-routing** graph only;
4. claim/package hygiene checks, including rejection of unlabeled reset edges and stale version references.

It explicitly does not report “proof passed.”

## 6. Version hygiene — rebuilt

All active files are named consistently with v5.0/v5_0. The final checksum file is generated from those exact files after PDF compilation and verification.

## Publication/prize status

This package should **not** be sent as a completed solution. It is the defensible intermediate artifact to use while proving P1 and P2. Restoring an unconditional theorem before those two obligations are closed would recreate the exact failure mode that the adversarial audits exposed.
