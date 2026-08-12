# Two-Player 3n ± 1 Game — v3.0 package

This package contains the self-contained manuscript and supporting verification artifacts.

## Files

- `3n_plus_minus_1_game_v3_0.pdf` — main article.
- `3n_plus_minus_1_game_v3_0.tex` — LaTeX source of the article.
- `verify_v3_0.py` — standalone finite arithmetic/control regression checks (Python standard library only).
- `routing_certificate_v3_0.json` — finite equal-rank control graph and rank-component inventory.
- `self_audit_v3_0.md` — adversarial self-audit of this exact package.
- `SHA256SUMS_v3_0.txt` — checksums of the package files.

## Supporting check

From the package directory run:

```bash
python verify_v3_0.py
```

Expected final lines:

```text
v3.0 supporting checks passed
maximum equal-rank control height: 9
```

The script and JSON certificate are supporting verification. They do not constitute an end-to-end formal proof of the infinite theorem; the mathematical argument is in the article.
