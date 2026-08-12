# 3n+-1 game article package

Files:

- `3n_plus_minus_1_game_v3_0.pdf` - compiled article.
- `3n_plus_minus_1_game_v3_0.tex` - LaTeX source.
- `verify_v3_0.py` - finite arithmetic regression checks for the identities used in the article.

Build PDF:

```bash
pdflatex 3n_plus_minus_1_game_v3_0.tex
pdflatex 3n_plus_minus_1_game_v3_0.tex
```

Run checks:

```bash
python verify_v3_0.py
```
