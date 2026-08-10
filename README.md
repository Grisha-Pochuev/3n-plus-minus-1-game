# Optimal `3n±1` Game

A rigorous and reproducible investigation of the two-player `3n±1` game
(also known as Conway's *Beans-Don't-Talk* game).

## Main claim and current status

Let `n > 1` be odd. A move chooses `3n+1` or `3n-1` and removes every factor
of two. Reaching `1` wins immediately.

The target theorem is:

> For every odd positive starting integer, optimal play reaches `1` after
> finitely many moves. Equivalently, the game has no `DRAW` positions.

**Current status on this repair branch: HUMAN-PROOF CLAIM RESTORED; INDEPENDENT RE-AUDIT PENDING.**

Ingo Althöfer's external audit found two genuine defects in the previous
Section 137: the proof confused decrease of the canonical odd coefficient
with decrease of its coefficient source, and it used the reverse-factor lemma
outside its exponent range. Both shortcuts remain withdrawn.

The repair now has two stages:

1. corrected Sections 136--138 in
   [`docs/verified-results.md`](docs/verified-results.md) withdraw the invalid
   inference and prove the universal factor/predecessor normalization;
2. [`docs/althoefer-audit-closure.md`](docs/althoefer-audit-closure.md) supplies
   the missing provenance/rank bridge. It proves the factor-free exponent-two
   base split and introduces a one-shot entry component that permits a returned
   inner source to be initialized once even when it exceeds the retained outer
   source. Re-entry can reset that component only after a genuine outer source
   or proof-token decrease.

The addendum therefore supersedes the `OPEN` conclusion at the end of the
historical corrected Sections 137--138 on this branch. The global no-`DRAW`
theorem is again claimed as a **human proof**, not as an end-to-end formal or
machine proof.

The most important audit distinction is unchanged:

- the new closure is a human mathematical argument;
- `certificates/global-routing.json` remains a **conditional** machine check of
  the declared typed assembly;
- the finite Python computations are supporting regressions, not an infinite
  proof;
- the current Lean project does not kernel-check the complete game theorem;
- independent external re-audit of the repaired bridge is still pending.

## Start here

For an independent check, begin with [`AUDIT.md`](AUDIT.md). The first-time
reader guide is [`START_HERE.md`](START_HERE.md). The shortest mathematical
reading route is:

1. [`docs/problem.md`](docs/problem.md) — exact rules and provenance;
2. [`docs/normal-form.md`](docs/normal-form.md) — binary conjugation;
3. Sections 14--17 of [`docs/verified-results.md`](docs/verified-results.md) — constant-tail coordinates and the original exponent-one obstruction;
4. Sections 79--81 and 87--90 — universal factor coupling and typed first-factor gates;
5. Sections 91--135 — obligation/factor normalizer and proof-token provenance;
6. corrected Sections 136--138 — the conservative audit repair before closure;
7. [`docs/althoefer-audit-closure.md`](docs/althoefer-audit-closure.md) — the one-shot attachment and restored final implication;
8. [`docs/global-proof.md`](docs/global-proof.md) — concise final assembly.

The published preprint remains archived at
[doi:10.5281/zenodo.21844684](https://doi.org/10.5281/zenodo.21844684). It
predates Althöfer's audit and should not be cited by itself as the current
proof text. The repair branch plus the closure addendum is the current audit
record.

## Reproduce the checks

Requirements: Python 3.10 or newer; no third-party Python packages.

Run:

```bash
python audit.py
```

The command checks repository layout, tests, finite arithmetic identities,
finite outcome certificates, and the declared symbolic routing assembly.
The symbolic stage may report `CONDITIONAL_MACHINE_CHECK`. That status still
means only that the declared typed control/rank graph passed its checker; the
new one-shot semantic bridge is a human-proof layer documented in the closure
addendum.

The main stages can also be run separately:

```bash
python -m unittest discover -s tests -v
python scripts/verify_claims.py --limit 100000
python scripts/verify_global_certificate.py
```

The new audit-closure arithmetic regressions are in
[`tests/test_althoefer_closure.py`](tests/test_althoefer_closure.py).

Optional larger experiments:

```bash
python scripts/retrograde_prefix.py --limit 1000000
python scripts/find_finite_draw_kernel.py --limit 1000000
python scripts/analyze_suffixes.py --limit 1000000 --suffix-bits 12
```

`UNKNOWN` in a bounded computation means only "not resolved by this
computation". It is neither a `DRAW` nor a counterexample.

### Lean

Lean is optional, pinned to version `v4.32.1`:

```bash
cd formal
lake update
lake build
```

See [`formal/COVERAGE.md`](formal/COVERAGE.md) before interpreting the result.
The current Lean project does not kernel-check the global no-`DRAW` theorem.

## Repository map

| Path | Purpose |
|---|---|
| [`AUDIT.md`](AUDIT.md) | independent audit protocol and current trust boundary |
| [`START_HERE.md`](START_HERE.md) | first-time reader guide |
| [`docs/althoefer-audit-repair.md`](docs/althoefer-audit-repair.md) | original external-audit repair and withdrawn shortcuts |
| [`docs/althoefer-audit-closure.md`](docs/althoefer-audit-closure.md) | closure of the remaining attachment lemma |
| [`docs/global-proof.md`](docs/global-proof.md) | concise restored global assembly |
| [`docs/verified-results.md`](docs/verified-results.md) | detailed local results and conservative corrected Sections 136--138 |
| [`docs/proof-map.md`](docs/proof-map.md) | dependency map including the closure addendum |
| [`src/optimal_3n1/`](src/optimal_3n1/) | exact arithmetic and bounded solvers |
| [`tests/`](tests/) | regression and soundness tests |
| [`certificates/`](certificates/) | finite proof DAGs and conditional typed-routing assembly |
| [`formal/`](formal/) | Lean project and explicit formalization coverage |
| [`paper/`](paper/) | article source and publication files; rebuild/re-audit before a new release |

## Status vocabulary

Local results keep their explicit statuses. The restored global theorem is a
**human-proof claim pending independent re-audit**. This must not be conflated
with the narrower machine or Lean verification scopes.

## Problem provenance

Ingo Althöfer's official page states the `3n+-1 game` problem addressed by
this repository and records Michael Hartisch's finite verification below one
million. See [`docs/problem.md`](docs/problem.md) for complete bibliographic
information.

- Official problem page: <https://althofer.de/collatz-prizes.html>
- Althöfer, Hartisch, Zipproth (2024), DOI:
  <https://doi.org/10.1007/978-3-031-54968-7_11>

## License

The repository is released under the [MIT License](LICENSE). Citation
metadata are provided in [`CITATION.cff`](CITATION.cff).
