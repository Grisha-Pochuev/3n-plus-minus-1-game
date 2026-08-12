# Two-Player 3n +/- 1 Game - Version 7.0

## Status

Version 7.0 is an **audited status manuscript**, not a claimed proof of the all-start no-DRAW conjecture. It withdraws every earlier unconditional closure claim that depended on unproved token provenance or router exhaustiveness.

The manuscript proves the local statements it labels as lemmas or propositions, retains the two decisive counterexamples to earlier shortcuts, and states the global conclusion only as a conditional theorem under four explicit open obligations:

- Z: source-zero valuation-one bootstrap and non-reseeding;
- H: provenance and continuity of the long high-return token pair;
- L: complete LOSS-anchored `D=2` module;
- E: semantically exhaustive marked router.

Accordingly:

- **PASS** as a logically self-contained status manuscript;
- **NOT A PASS** as a solution submitted for the EUR 500 prize;
- no end-to-end Lean formalization is claimed.

## Files

- `3n_plus_minus_1_game_v7.0.pdf` - typeset manuscript;
- `3n_plus_minus_1_game_v7.0.tex` - LaTeX source;
- `verify_v7_0.py` - dependency-free supporting arithmetic regressions;
- `verification_output_v7.0.txt` - output of the large regression run;
- `AUDIT_REPORT_v7.0.md` - hostile-audit report and version lineage;
- `pdf_inspect_v7.0.txt` and `pdf_preflight_v7.0.txt` - PDF structural checks;
- `SHA256SUMS_v7.0.txt` - hashes of the release files.

## Rebuild

A recent TeX Live installation with `latexmk` is sufficient:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  3n_plus_minus_1_game_v7.0.tex
```

The release PDF was built without undefined references, LaTeX warnings, overfull boxes, or underfull boxes.

## Supporting regression run

A quick default run:

```bash
python verify_v7_0.py
```

The release run used:

```bash
python verify_v7_0.py \
  --limit 500000 \
  --source-limit 100000 \
  --coeff-limit 20000 \
  --max-r 22 \
  --max-k 10 \
  --max-v 22 \
  --zero-n 250 \
  --random-samples 10000 \
  --random-bits 512
```

Finite regressions are supporting evidence only. They do not classify the infinite game and do not discharge Obligations Z, H, L, or E.

## Source lineage reviewed

The audit compared the available manuscripts and packages from v1, v2, v3.0, v4.0, v5.0, and v6.3, together with the detailed `docs/verified-results.md` ledger and the repair branch of the repository. No assertion was imported into v7.0 merely because an earlier manuscript called it proved.
