# Two-player 3n +/- 1 game — v6.3 audit-hardened package

Files:

- `3n_plus_minus_1_game_v6.3.pdf` — reviewed 34-page article;
- `3n_plus_minus_1_game_v6.3.tex` — LaTeX source;
- `verify_v6_3.py` — standalone arithmetic/control regressions;
- `verify_structure_v6_3.py` — structural red/orange audit checks;
- `routing_certificate_v5_0.json` — frozen prior control inventory used by the structural comparison;
- `AUDIT_REPORT_v6.3.md` — audit history, final checks, and trust boundary;
- `SHA256SUMS.txt` — file hashes.

Recommended checks:

```bash
python verify_structure_v6_3.py
python verify_v6_3.py --limit 500000 --random-samples 10000 --random-bits 512
```

The Python checks support the human proof; they are not an end-to-end formal proof.
