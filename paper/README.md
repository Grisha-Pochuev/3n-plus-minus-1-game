# Article draft

`main.tex` is a repository-only working manuscript. It is not submitted or
published automatically, and no repository script contacts a journal,
preprint server, or prize organizer.

The manuscript gives the problem, normal form, final rank architecture, and
global proof. The detailed 138-section proof is treated as an accompanying
supplement in `../docs/verified-results.md`. Before any external submission,
the manuscript and supplement need independent mathematical review and the
bibliography should be checked against the target venue's style.

Suggested build:

```bash
pdflatex main.tex
bibtex main
pdflatex main.tex
pdflatex main.tex
```

No TeX compiler was available during the initial repository packaging, so a
PDF is not committed until the source has actually been compiled and visually
checked.
