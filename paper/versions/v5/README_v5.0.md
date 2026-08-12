# Two-player 3n ± 1 game — version 5.0 audit-hardened package

Date: 10 August 2026

## Status

This package is deliberately **claim-safe**. It does not claim that the €500 no-DRAW prize problem has been solved.

Version 4.0 repaired two earlier defects but a subsequent adversarial audit found that the global routing argument still used an unjustified retained-anchor comparison after a multi-A streak and that the semantic completeness of the factor/high-return router had not been proved. Version 5.0 removes those claims rather than hiding them in a larger rank.

The proved part is presented as a rigorous reduction. The two remaining global composition obligations are P1 and P2 in `OPEN_PROOF_OBLIGATIONS_v5_0.md`.

## Files

- `3n_plus_minus_1_game_v5.0.pdf` — audit-hardened manuscript.
- `3n_plus_minus_1_game_v5.0.tex` — LaTeX source.
- `verify_v5_0.py` — supporting arithmetic, negative-regression, package, and finite-control checks.
- `routing_certificate_v5_0.json` — finite routing inventory with every reset explicitly labelled as proved-strict or OPEN-P1/P2.
- `OPEN_PROOF_OBLIGATIONS_v5_0.md` — exact remaining mathematical obligations and acceptance criteria.
- `SELF_AUDIT_v5.0.md` — adversarial self-audit of this package.
- `REPAIR_REPORT_v5.0.md` — mapping from the v4.0 findings to the v5.0 repair.
- `SOURCE_REVISION_v5.0.md` — immutable repository revision inspected as supporting evidence.
- `verification_output_v5.0.txt` — output of the final supporting verification run.
- `SHA256SUMS_v5.0.txt` — hashes of the package files (excluding the checksum file itself).

## Permanent negative tests

Future versions must continue to reproduce both counterexamples:

1. **Coefficient/source separation:** with `s=1`, `J(s)=5`, `a=15`, `e=1`, the boundary child is 22, whose canonical coefficient is 11 but whose source is 3. Hence a smaller coefficient does not imply a smaller source in the presence of powers of three.
2. **Pre-streak anchor separation:** `20 -> 30 -> 45 -> 68` and `B(68)=25>20`. Hence a high-valuation B transfer after several A steps does not imply descent below the source retained before the streak.

`verify_v5_0.py` fails if either negative test stops reproducing the forbidden inference.

## Running the checks

```bash
python verify_v5_0.py
```

A successful run means only that the stated finite/arithmetic checks and claim-safety guards passed. It does **not** prove P1, P2, or the infinite no-DRAW theorem.
