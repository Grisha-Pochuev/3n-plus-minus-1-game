# Adversarial self-audit — version 5.0

## Verdict

**No hidden unconditional theorem claim.** Version 5.0 is a rigorous reduction plus an explicit list of two unresolved global composition obligations. It should therefore not fail a future audit for the already known reason “a finite routing certificate was presented as a complete proof.”

This is not the same as saying that no future auditor can find a new error in a proved local lemma. No finite review can guarantee that. The design goal is narrower and checkable: every currently known global gap is visible, named, and excluded from the theorem claim.

## Finding A — coefficient/source confusion

**Former failure:** a smaller canonical coefficient was treated as a smaller coefficient source even when powers of three were present.

**Permanent counterexample:** `s=1`, `J(s)=5`, `a=15`, `e=1`; the common child is 22, with coefficient 11 = `J(3)`, so the source grows `1 -> 3`.

**v5.0 action:** the manuscript permits coefficient-to-source descent only in an explicitly factor-free `J(x)` setting or after a separately proved source formula. The counterexample is in the PDF and the verifier.

**Status:** CLOSED as a claim-hygiene issue; future mathematical uses still require local checking.

## Finding B — retained anchor after a multi-A streak

**Former failure:** a B-selecting transfer was compared with the source retained before several expanding A steps.

**Permanent counterexample:** `20 -> 30 -> 45 -> 68`, followed by the selected valuation-three return `B(68)=25>20`.

**v5.0 action:** A-streak integers are temporary cursors. The edge `b_select -> factor_fork` is pure routing, not a source descent. Any upward control reset after a valuation-two return is marked `OPEN-P1` until a real descendant/source certificate is supplied.

**Status:** the false inference is CLOSED; the positive reset-provenance theorem is OPEN as P1.

## Finding C — semantic completeness of the router

**Former failure:** names such as `factor_fork` and `high_return` were given a finite control graph, but the proof did not fully derive every control transition from actual game states and outcome-compatible DRAW choices.

**v5.0 action:** the JSON graph is explicitly bookkeeping only. The mathematical completeness theorem is OPEN as P2. Every high-control reset in the JSON is labelled `OPEN-P2` rather than silently treated as equal-rank routing.

**Status:** OPEN as P2; no unconditional theorem depends on it in v5.0.

## Finding D — valuation-two recycle token

**Former failure:** repeated valuation-two returns were said to lower a proof token without a complete comparison through arbitrary multi-A streaks.

**v5.0 action:** this is included explicitly in P1. “WIN”, “smaller than the immediate cursor”, and “valuation two” are all listed as insufficient evidence.

**Status:** OPEN as P1.

## Finding E — finite control versus proof

**Former failure:** an acyclic declared control graph could be mistaken for semantic well-foundedness.

**v5.0 action:** the verifier checks only the pure-routing subgraph. Open reset edges are omitted from that acyclicity claim and must carry `OPEN-P1` or `OPEN-P2`. The script rejects unlabeled resets.

**Status:** CLOSED as a verification-scope issue.

## Finding F — package version drift

**Former failure:** files named v4.0 still referred to v3.0 JSON, verifier output, and README text.

**v5.0 action:** all package-facing names are v5.0/v5_0; the verifier scans the manuscript and package documents for stale `v3_0`, `v3.0`, `v4_0`, and `v4.0` references outside this historical audit file. Checksums are generated only after the final files are built.

**Status:** CLOSED in the generated package.

## What a hostile reviewer should attack next

1. Try to prove or refute P1 using an explicit multi-A streak followed by a valuation-two reset, including exceptional sources.
2. Build the full semantic transition table required by P2 and search for a DRAW-compatible row not covered by the declared controls.
3. Re-run the two permanent negative tests against every future proposed rank.
4. Treat every statement imported from a moving repository supplement as unproved unless its exact version/commit and lemma are included in the submitted package.

## Claim boundary

The PDF proves the displayed local arithmetic and conditional implication. It does not prove P1 or P2 and therefore does not claim the prize theorem. Any later version that restores an unconditional theorem must contain proofs of both obligations in the frozen package itself.
