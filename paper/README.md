# Article source

`main.tex` is the English preprint intended for a Zenodo
**Publication / Preprint** record. It includes the author's correspondence
address, the verification repository, the proof architecture, reproducibility
commands, and an explicit distinction between the human proof, conditional
global certificate, finite regression evidence, and Lean-checked metatheory.

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

## Manuscript history

The complete preserved development line is stored in [`history/`](history/):

```text
v1 -> v2 -> v3.0 -> v4.0 -> v5.0 -> v6.3 -> v7.0 -> ...
```

The history directory is append-only in spirit. Old snapshots are retained as they were so that the evolution of the proof, audits, repairs, and verification code remains inspectable. Historical versions may contain arguments that were later superseded or found incomplete; `main.tex` / `main.pdf` remain the current working manuscript.

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
