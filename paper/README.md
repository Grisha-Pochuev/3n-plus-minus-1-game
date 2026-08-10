# Article source

The published Zenodo record predates the external Althöfer audit:
<https://doi.org/10.5281/zenodo.21844684>.

The repository now contains a human-proof closure of the audit gap in
`../docs/althoefer-audit-closure.md`.  **The current `paper/main.tex` has not
yet been rewritten to incorporate that 10 August closure and should therefore
be treated as the conservative pre-closure repair draft, not as the current
authoritative proof text.**

This deliberate publication hold avoids replacing one premature proof claim
with another.  Before a new preprint version is released, the closure addendum
should be independently re-audited and then integrated into `main.tex` as one
coherent manuscript.

The authoritative current mathematical status is in:

- `../AUDIT.md`;
- `../docs/althoefer-audit-repair.md` — the withdrawn shortcuts and
  conservative intermediate repair;
- `../docs/althoefer-audit-closure.md` — the new one-shot attachment proof;
- `../docs/global-proof.md` — the restored global assembly;
- `../docs/proof-ledger-closure.md` — the status overlay superseding the final
  OPEN rows of the historical proof ledger.

No current `main.pdf` should be cited as the post-closure proof unless it has
been rebuilt from a manuscript that includes the closure and its independent
review status.

## Build

With a conventional TeX installation:

```bash
cd paper
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

With Tectonic:

```bash
cd paper
tectonic main.tex
```

These commands only render the source; they do not validate the mathematics.
Before any new release, inspect every rendered page and confirm that the
abstract, theorem status, audit history, closure lemma, bibliography, URLs,
formulas, and page numbers all match the reviewed repository proof.

## Zenodo bundle

**Do not publish a new proof version merely because the closure addendum now
exists.**  First obtain an independent re-audit of the repaired bridge.  After
that review and integration into `main.tex`, the bundle can be rebuilt with

```bash
python scripts/build_zenodo_bundle.py
```

and reviewed according to `../zenodo/UPLOAD_CHECKLIST.md`.

## Licensing

The article and its source are CC BY 4.0; see `LICENSE.md`. Verification
software remains under the repository's root MIT license.
