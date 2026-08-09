# Article source

`main.tex` is now an **audited repair draft**, not a completed proof manuscript.

The published Zenodo record predates the external audit:
<https://doi.org/10.5281/zenodo.21844684>.

Ingo Althöfer's audit exposed a genuine gap in the old Section 137.  The
repository repair proves a universal two-level arithmetic normalization for
the omitted factorful exponent-one family, but the provenance/rank attachment
lemma stated in corrected Section 137 remains open.  Accordingly the paper
source on this branch must not claim that the global no-`DRAW` theorem is
proved.

The authoritative technical status is in:

- `../AUDIT.md`;
- `../docs/althoefer-audit-repair.md`;
- corrected Sections 136--138 of `../docs/verified-results.md`;
- `../docs/global-proof.md`.

`main.pdf` on this branch may still be an older rendered artifact until the
corrected `main.tex` is rebuilt; do not cite the PDF without checking its
revision.

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

Before any new release, inspect every rendered page and confirm that the
abstract, theorem status, audit note, bibliography, URLs, formulas, and page
numbers match the repaired source.

## Zenodo bundle

Do not publish a new proof version while the attachment lemma is open.  After
a future completion is independently re-audited, the bundle can be rebuilt
with

```bash
python scripts/build_zenodo_bundle.py
```

and reviewed according to `../zenodo/UPLOAD_CHECKLIST.md`.

## Licensing

The article and its source are CC BY 4.0; see `LICENSE.md`.  Verification
software remains under the repository's root MIT license.
