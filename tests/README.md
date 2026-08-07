# Tests

Run all tests from the repository root:

```bash
python -m unittest discover -s tests -v
```

The suite has three layers:

- `test_game.py` checks exact arithmetic identities and regression cases from
  the mathematical proof;
- `test_retrograde.py` checks soundness invariants of bounded `WIN`/`LOSS`
  propagation;
- `test_certificates.py` checks that the independent certificate verifier
  accepts valid witnesses and rejects malformed edges, ranks, and padding.

A passing test suite shows that the implementation matches these cases. It is
not, by itself, a proof over all integers.
