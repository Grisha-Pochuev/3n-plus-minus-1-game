# Mathematical documentation

## Current research status — read this first

The no-DRAW theorem is **OPEN — RED**. Do not treat the historical manuscripts or
`global-proof.md` as a completed proof. The current clean restart deliberately avoids
patching Section 136 in place.

| File | Role | Read when |
|---|---|---|
| `problem.md` | exact game, sources, outcome terminology | first |
| `proof-architecture-reset-2026-08-14.md` | decision to stop patching the old global rank and restart from trusted local lemmas | second |
| `pro-session-high-return-frontier-2026-08-14.md` | strongest high-return provenance results and explicit falsifications | third |
| `whole-problem-certificate-reduction-2026-08-20.md` | clean whole-problem reduction to finite-certificate transport `Fin(D(n)) -> Fin(U(n))`; current frontier | **current handoff** |
| `verified-results.md` | library of locally proved arithmetic/outcome lemmas; not by itself a global proof | as needed |
| `pitfalls.md` | known false shortcuts and counterexamples | before accepting any new global argument |

## Historical / frozen proof architecture

| File | Status |
|---|---|
| `global-proof.md` | historical proof assembly; **not accepted as a completed theorem after the provenance audit** |
| `proof-map.md` | map of the historical assembly |
| `proof-ledger.md` | detailed claim-status record; use together with the newer reset/handoff notes |
| `high-return-lifecycle-handoff-2026-08-14.md` | exact lifecycle gap and acceptance criteria |
| `high-return-provenance-obligation.md` | occurrence-provenance obligation for long high returns |
| `d2-loss-anchored-obligation.md` | local D=2 module; globally conditional on legal incoming-token carry |
| `certificate-transport-shadow-lemma-2026-08-14.md` | partial shadow-word provenance theorem; not global closure |

## Independent certificate checker

`../scripts/check_game_certificates.py` independently checks concrete finite WIN/LOSS
proof trees and finite coinductive DRAW traps. It deliberately does **not** infer the
infinite theorem from bounded search.

Self-test:

```bash
python scripts/check_game_certificates.py --self-test
```

Expected output is recorded in
`whole-problem-certificate-checker-selftest-2026-08-20.txt`.

## Reproducibility records

| File | Meaning |
|---|---|
| `audit-run-2026-08-07.md` | historical packaging run and exact parameters |
| `baseline-run.md` | earlier historical baseline; test count is intentionally older |

## Research history

| File | Meaning |
|---|---|
| `research-plan.md` | chronological development; not the current status page |
| `unverified-leads.md` | ideas intentionally not promoted to proved statements |
| `handoff-ru.md` | older Russian-language handoff note |

For new work, start from the current research-status table above rather than from a
theorem-claiming manuscript.
