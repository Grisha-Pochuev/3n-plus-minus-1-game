# Independent audit guide

This document tells a third party exactly what is claimed, what can be checked
mechanically, and where human mathematical review is still required.

## 1. Claim under review

**OPEN.** The proposed human proof does not currently establish that every
odd positive starting value has finite remoteness. One decisive global
obligation remains: the long high-return transition has not shown that its
pair `u,c` consists of already retained token occurrences, nor that the
resulting marked pair is carried without reseeding to its next strict
payment. The formerly separate unbounded `D=2` row now has such a local
payment from its retained `q` occurrence, but it does not install that
occurrence. The required installation/carry/no-reseed theorem remains open. See
[`docs/high-return-provenance-obligation.md`](docs/high-return-provenance-obligation.md)
and [`docs/d2-loss-anchored-obligation.md`](docs/d2-loss-anchored-obligation.md).

## 2. Trust boundary

An audit has four separate layers.

| Layer | What it establishes | What it does not establish |
|---|---|---|
| Human proof | Local reductions and a conditional proof architecture | The unconditional infinite theorem; the open lifecycle obligation above invalidates the current global assembly |
| Global assembly certificate | Totality of the declared symbolic partitions, one rule per declared case, valid lexicographic reset discipline, and no equal-rank control cycle | That the declared macro guards and effects refine every legal game continuation |
| Python arithmetic and finite certificates | Exact implementation agreement on stated finite ranges and genuine finite `WIN`/`LOSS` proof DAGs | The theorem for all integers |
| Lean build | Exact original/conjugated moves, finite outcomes, token and macro ranks, the control DAG, and the conditional theorem marked Lean-proved in `formal/COVERAGE.md` | Construction of the concrete JSON-to-game refinement or the unconditional global no-`DRAW` theorem |

No bounded `UNKNOWN` position is called a draw. No finite cutoff is used as a
substitute for well-foundedness.

The symbolic certificate has four mandatory `HUMAN_PROOF` obligations:

1. the universal arithmetic and coordinate identities behind its macros;
2. refinement of the declared semantic guards to every legal case;
3. outcome compatibility of the selected `DRAW` continuation and carried
   finite tokens;
4. finite productivity of every macro normalization.

The checker refuses a certificate that omits or relabels any of these. See
[`certificates/global-routing-certificate.md`](certificates/global-routing-certificate.md).

## 3. Fast reproducibility check

From a clean checkout, record the exact revision:

```bash
git rev-parse HEAD
git status --short
python --version
```

Then run:

```bash
python audit.py
```

This command validates repository layout and links, scans Lean sources for
unfinished placeholders, runs the complete tests, checks finite arithmetic,
checks the conditional global assembly, and independently validates both a
committed and a freshly generated finite outcome certificate.

The current clean-clone output is recorded in
[`docs/audit-run-2026-08-08.md`](docs/audit-run-2026-08-08.md).

The global stage can be isolated:

```bash
python scripts/verify_global_certificate.py
```

Acceptance must be quoted together with its printed status
`CONDITIONAL_MACHINE_CHECK` and the four remaining obligations.

For the formalized subset:

```bash
cd formal
lake update
lake build
```

The Lean toolchain is pinned to `v4.32.1`; the project has no third-party Lean
dependency. Read [`formal/COVERAGE.md`](formal/COVERAGE.md) before reporting
the scope of a successful build.

## 4. Human proof audit

Read the proof in this order:

1. Confirm the game semantics and the `WIN`/`LOSS`/`DRAW` trichotomy in
   [`docs/problem.md`](docs/problem.md).
2. Verify the binary normal form in [`docs/normal-form.md`](docs/normal-form.md),
   especially the unbounded alternating-suffix operation.
3. Read the short assembly in [`docs/global-proof.md`](docs/global-proof.md).
4. Compare the certificate inventory with
   [`certificates/global-routing.json`](certificates/global-routing.json).
5. Use [`docs/proof-map.md`](docs/proof-map.md) to expand every cited
   dependency.
6. Check Sections 129–138 of
   [`docs/verified-results.md`](docs/verified-results.md) line by line, then
   follow their backward citations.
7. Compare every dependency and status with
   [`docs/proof-ledger.md`](docs/proof-ledger.md).
8. Check the proposed reasoning against every failure mode in
   [`docs/pitfalls.md`](docs/pitfalls.md).

## 5. Decisive manual obligations

Try to falsify these links first:

- the Section 137 source/token/normalizer trichotomy really covers every
  minimum-source and height-one continuation;
- every semantic case in `global-routing.json` corresponds to exactly the
  game cases cited by its `proof_sections` field;
- the source/proof-token projection never increases, including on resets;
- every token-changing edge replaces actual carried tokens by certified lower
  descendants;
- the equal-projection normalizer has no hidden parameterized recurrence not
  represented in the finite control DAG;
- every high-return cross-transition is strict before a fresh marked task can
  be installed;
- a hypothetical `DRAW` really supplies another marked configuration after a
  finite macro normalization;
- the terminal `q=0` conclusion is transported correctly to all odd original
  states, including values divisible by three.

The checker detects an omitted *declared* guard case. It cannot detect that a
human-defined guard partition omitted a genuine arithmetic possibility. That
distinction is the central remaining trust boundary.

## 6. How to report a problem

A useful report should identify the smallest precise failing item:

- certificate transition identifier or document section;
- exact statement being challenged;
- assumptions available at that point;
- a counterexample, failed inference, or missing case;
- whether the issue affects a local lemma, certificate refinement, dependency
  map, or the global theorem.

Arithmetic counterexamples should include a minimal input and a short script
or calculation. Proof gaps should distinguish an omitted explanation from a
false statement.

## 7. Current audit status

- Unconditional human proof: **OPEN; HOSTILE AUDIT FAILED**.
- Long high-return token provenance: **OPEN — RED**.
- Unbounded `D=2` local token payment: **PROVED, conditional on the incoming marked occurrence**.
- Symbolic global assembly: **CONDITIONAL MACHINE CHECK IMPLEMENTED**.
- Python regression suite: **COMPUTATIONALLY VERIFIED** at the recorded
  revision.
- Finite identity run through 100000: **COMPUTATIONALLY VERIFIED** at the
  recorded revision.
- Lean normal form, outcome layer, token/macro ranks, control DAG, and
  conditional no-`DRAW` bridge: **KERNEL-CHECKED BUILD**, with exact
  limitations in `formal/COVERAGE.md`.
- Concrete certificate-to-game refinement in Lean: **PENDING**.
- Independent external review: **PENDING**.
