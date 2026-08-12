# Final corrected manuscript package

Files:

- `3n_plus_minus_1_game_final.pdf` - corrected English article.
- `3n_plus_minus_1_game_final.tex` - self-contained LaTeX source; it compiles with `pdflatex` and does not require BibTeX.
- `references.bib` - reusable bibliography entries for a future journal template.
- `verify_closure.py` - standalone finite regression for the new Althoefer-audit closure identities. It uses only the Python standard library.

## Proof status

The article restores the global no-DRAW statement as a **human-proof claim** after the entry repair developed on the repository branch `repair/althoefer-audit-gap`. The two invalid shortcuts found by the external audit remain withdrawn. Independent external re-audit is still pending, and neither the JSON routing certificate nor the Lean subset is presented as an end-to-end formal proof.

The older Zenodo record `10.5281/zenodo.21844684` predates the audit and should not be treated as the corrected final manuscript.

## Build

```bash
pdflatex -interaction=nonstopmode -halt-on-error 3n_plus_minus_1_game_final.tex
pdflatex -interaction=nonstopmode -halt-on-error 3n_plus_minus_1_game_final.tex
```

## Arithmetic regression

```bash
python verify_closure.py --limit 200000
```

A passing finite regression supports the exact identities used in the repaired bridge; it is not a proof of the infinite theorem.
