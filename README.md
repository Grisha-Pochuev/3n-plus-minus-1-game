# Optimal `3n±1` Game

A proof repository for the two-player `3n±1` game (also known as Conway's
*Beans-Don't-Talk* game).

## Main claim

Let `n > 1` be odd. A move chooses `3n+1` or `3n-1` and removes every factor
of two. Reaching `1` wins immediately. The repository proves:

> **PROVED (human proof).** For every odd positive starting integer, optimal
> play reaches `1` after finitely many moves. Equivalently, the game has no
> `DRAW` positions.

The concise assembly is in [`docs/global-proof.md`](docs/global-proof.md).
The complete chain of local lemmas is in
[`docs/verified-results.md`](docs/verified-results.md), with claim-by-claim
status in [`docs/proof-ledger.md`](docs/proof-ledger.md).

Important audit distinction:

- the complete theorem is claimed as a **human proof**;
- the symbolic global-routing certificate machine-checks the declared finite
  assembly and rank logic, conditional on four explicit human refinement and
  outcome obligations;
- the Python suite checks exact identities and finite instances, but is not
  presented as a proof of the infinite theorem;
- Lean checks the foundations and the general well-founded-certificate
  metatheorem listed in [`formal/COVERAGE.md`](formal/COVERAGE.md); the global
  theorem is **not yet Lean-checked**;
- independent external review is still pending.

## Start here

For an independent check, begin with [`AUDIT.md`](AUDIT.md). The first-time
reader guide is [`START_HERE.md`](START_HERE.md). The shortest mathematical
reading route is:

1. [`docs/problem.md`](docs/problem.md) — exact rules and provenance;
2. [`docs/normal-form.md`](docs/normal-form.md) — binary conjugation;
3. [`docs/global-proof.md`](docs/global-proof.md) — global no-`DRAW` argument;
4. [`docs/proof-map.md`](docs/proof-map.md) — dependency map into the detailed proof;
5. [`docs/proof-ledger.md`](docs/proof-ledger.md) — status of every major claim;
6. [`docs/verified-results.md`](docs/verified-results.md) — all detailed lemmas;
7. [`docs/pitfalls.md`](docs/pitfalls.md) — known invalid shortcuts.

The article draft lives only in this repository under [`paper/`](paper/).
No submission or publication is performed by repository tooling.

## Reproduce the checks

Requirements: Python 3.10 or newer; no third-party Python packages.

For the simplest independent check, run one command from the repository root:

```bash
python audit.py
```

It runs the complete test suite, finite identity checks, validates the
conditional global-routing assembly, generates a finite outcome proof
certificate, and validates that certificate with a separate small checker.
Its scope and limitations are documented in
[`certificates/README.md`](certificates/README.md).

The same main stages can be run separately:

```bash
python -m unittest discover -s tests -v
python scripts/verify_claims.py --limit 100000
python scripts/verify_global_certificate.py
```

Expected result: `107` tests pass, followed by verification of the normal form
and descent identities through `100000`, and acceptance of a 46-transition
global assembly with status `CONDITIONAL_MACHINE_CHECK`. The earlier packaging
baseline is [`docs/audit-run-2026-08-07.md`](docs/audit-run-2026-08-07.md); the
current command always prints the checked revision's live result.

Optional larger experiments:

```bash
python scripts/retrograde_prefix.py --limit 1000000
python scripts/find_finite_draw_kernel.py --limit 1000000
python scripts/analyze_suffixes.py --limit 1000000 --suffix-bits 12
python scripts/extract_proof.py 100 --limit 1000000 --output results/proof-100.json
```

`UNKNOWN` in a bounded computation means only "not resolved by this
computation". It is neither a `DRAW` nor a counterexample.

### Lean

Lean is optional, pinned to version `v4.32.1`, and the current project has no
third-party Lean dependency:

```bash
cd formal
lake update
lake build
```

See [`formal/README.md`](formal/README.md) and
[`formal/COVERAGE.md`](formal/COVERAGE.md) before interpreting the result.

## Repository map

| Path | Purpose |
|---|---|
| [`AUDIT.md`](AUDIT.md) | independent verification protocol and trust boundary |
| [`START_HERE.md`](START_HERE.md) | first-time reader guide with commands and expected results |
| [`docs/global-proof.md`](docs/global-proof.md) | concise proof of the main theorem |
| [`docs/verified-results.md`](docs/verified-results.md) | detailed mathematical proof, Sections 1–138 |
| [`docs/proof-ledger.md`](docs/proof-ledger.md) | status and dependencies of claims |
| [`docs/proof-map.md`](docs/proof-map.md) | roadmap through the final dependency chain |
| [`src/optimal_3n1/`](src/optimal_3n1/) | exact arithmetic and bounded solvers |
| [`tests/`](tests/) | regression and soundness tests |
| [`scripts/`](scripts/) | reproducible verification and exploration |
| [`certificates/`](certificates/) | finite proof DAGs and the conditional symbolic global assembly |
| [`formal/`](formal/) | Lean project and explicit formalization coverage |
| [`paper/`](paper/) | article source kept in the repository only |

## Status vocabulary

Every research claim is classified as `PROVED`, `COMPUTATIONALLY VERIFIED`,
`CONJECTURE`, `DISPROVED`, or `UNVERIFIED LEAD`. These labels are defined and
enforced in [`AGENTS.md`](AGENTS.md).

## Provenance and prize

Ingo Althöfer's official page describes the `3n+-1 game`, a €500 prize, and
a submission deadline of 31 December 2037. It also records Michael Hartisch's
finite verification below one million. See
[`docs/problem.md`](docs/problem.md) for the earlier Beans-Don't-Talk sources
and complete bibliographic information.

- Official prize page: <https://althofer.de/collatz-prizes.html>
- Althöfer, Hartisch, Zipproth (2024), DOI:
  <https://doi.org/10.1007/978-3-031-54968-7_11>

## License

The repository is released under the [MIT License](LICENSE). Citation
metadata are provided in [`CITATION.cff`](CITATION.cff).
