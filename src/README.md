# Python library

The importable package is `optimal_3n1`.

| Module | Responsibility |
|---|---|
| `game.py` | exact original and conjugated moves, binary suffix operations, source/tail coordinates |
| `retrograde.py` | boundary-safe bounded outcome propagation and finite proof witnesses |
| `analysis.py` | streaming helpers for experiments |
| `transducer.py` | finite-state Gray-code transition machinery |

The core code uses only the Python standard library. Mathematical statements
about these functions are documented in `docs/normal-form.md` and
`docs/verified-results.md`; tests are not silently promoted to theorems.
