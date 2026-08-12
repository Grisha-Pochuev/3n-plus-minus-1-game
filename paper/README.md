# Article source

## Hostile-audit deliverable (12 August 2026)

`audit_ready_reduction.tex` is the self-contained article that passed the
claim-by-claim hostile audit recorded in
`HOSTILE_AUDIT_AUDIT_READY_REDUCTION.md`.  Its compiled PDF is
`../output/pdf/audit_ready_reduction.pdf`.

The pass is deliberately scoped: this is a rigorous reduction, local-repair,
and gap-report article.  It proves every theorem it asserts, but it does not
claim the still-open unconditional no-DRAW theorem.  Advertising it as a
complete solution would invalidate the audit verdict.

The historical article archive is in [`versions/`](versions/). Drafts v1--v6
are preserved there for provenance, the attached release package is version
7.0, and the audit-ready article produced on 12 August 2026 is version 8.0.

`main.tex` is an English hostile-audit draft. It currently presents a rigorous
conditional proof architecture, not a proof of the unconditional theorem. The
shared long high-return token installation/carry/no-reseed lifecycle remains
open.  The unbounded `D=2` row has a local strict payment conditional on its
incoming marked occurrence, but does not install that occurrence. Do not
publish or describe this revision as a completed solution.

Published record: <https://doi.org/10.5281/zenodo.21844684>.

No repository script uploads or publishes the article. The author performs the
final Zenodo review and publication.

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

The repository uses only common LaTeX packages. Before release, inspect every
rendered PDF page and confirm that bibliography entries, URLs, formulas, page
numbers, and the email link render correctly.

## Zenodo bundle

After the PDF exists and all changes are committed, run from the repository
root:

```bash
python scripts/build_zenodo_bundle.py
```

This produces the exact upload files in `dist/zenodo/`. Follow
[`../zenodo/UPLOAD_CHECKLIST.md`](../zenodo/UPLOAD_CHECKLIST.md) before pressing
Zenodo's `Publish` button.

## Licensing

The article and its source are CC BY 4.0; see [`LICENSE.md`](LICENSE.md). The
verification software linked from the article remains under the repository's
root MIT license.
