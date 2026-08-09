# Independent audit guide

This document tells a third party exactly what is currently established,
what can be checked mechanically, and what remains open after the external
audit of Sections 136--138.

## 1. Current claim status

**GLOBAL THEOREM: OPEN IN THIS MANUSCRIPT.**

The intended theorem is that every odd positive starting value in the
two-player `3n±1` game has finite remoteness, equivalently that the
conjugated game has no `DRAW` positions and optimal play reaches `1`.

The previous repository revision labelled this theorem `PROVED (human
proof)`.  Ingo Althöfer reported an independent audit that found a genuine
entry gap in old Section 137.  The repair branch withdraws the invalid
inference, proves an exact two-level normalization for the missing
factorful exponent-one arithmetic family, and isolates the remaining
source/proof-token attachment lemma.  Independent re-review of any future
completion is still required.

## 2. The audited defect

The old Section 137 inferred a decrease of the coefficient **source** from a
decrease of the canonical odd coefficient.  This is false in the presence
of powers of three.  A concrete counterexample is

\[
s=1,\quad J(1)=5,\quad a=3J(1)=15,\quad \epsilon=1,
\]

for which

\[
R(3a-\epsilon)=R(44)=22.
\]

The new canonical coefficient is \(11<15\), but \(11=J(3)\), so the new
source is \(3>1\).

The old proof also used Section 16 as though it removed powers of three at
constant-tail exponent one.  It does not.  Thus an arbitrary state

\[
Q_1^\epsilon(3^kJ(s)),\qquad k>0,
\]

was not covered by the old entry trichotomy.

## 3. What the repair establishes

Corrected Section 137 applies the universal factor-level results of Sections
79--81 directly to the missing family.  If the displayed factorful
exponent-one state is DRAW, then within the current or next factor level a
DRAW exit occurs.  Factoring

\[
3^{i+1}J(s)+1-2\epsilon=2^vJ(t)
\]

gives the exact signed exit

\[
Q_v^{1-\epsilon}(J(t)).
\]

For \(v\ge2\), the raw sibling is exactly

\[
Q_{v-1}^{1-\epsilon}(J(t));
\]

for \(v=1\), a positive raw DRAW has a strict coefficient-source descent
relative to \(t\).  This is a complete arithmetic normalization of the
previously omitted family.

What is **not** yet proved is that the returned source \(t\) can always be
attached to the retained outer rank without increase.  In general \(t>s\)
can occur.  The corrected proof therefore does not replace the old source
anchor by \(t\).

The remaining statement is named the **arbitrary exponent-one attachment
lemma** in Section 137.  It must show that the normalized DRAW continuation
produces a genuine lower retained source, a certified lower proof token, or
a typed entry to Section 136 while preserving the retained outer data.

## 4. Trust boundary

An audit has four separate layers.

| Layer | What it establishes | What it does not establish |
|---|---|---|
| Human local proofs | The individual arithmetic/outcome lemmas with their stated hypotheses | The missing global attachment lemma |
| Symbolic routing certificate | The declared finite control/rank assembly for typed entries | That every real game continuation reaches one of those typed entries |
| Python arithmetic and finite certificates | Exact implementation agreement on stated finite ranges and genuine finite `WIN`/`LOSS` proof DAGs | The infinite no-`DRAW` theorem |
| Lean build | Definitions and metatheorems listed in `formal/COVERAGE.md` | The concrete JSON-to-game refinement or the global no-`DRAW` theorem |

The symbolic checker may still print `CONDITIONAL_MACHINE_CHECK`.  After the
external audit this must be read narrowly: it checks the declared typed
assembly, not the unresolved semantic attachment of the arbitrary
factorful exponent-one family.

## 5. Reproducibility checks

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

The local tests, finite arithmetic checks, finite outcome certificates, and
the declared symbolic routing certificate remain useful.  A successful run
must **not** be described as a proof of the global theorem.

The symbolic stage can be isolated with

```bash
python scripts/verify_global_certificate.py
```

and the Lean subset with

```bash
cd formal
lake update
lake build
```

Read `formal/COVERAGE.md` before interpreting a successful Lean build.

## 6. Human proof audit order

Read the mathematics in this order:

1. `docs/problem.md` — game semantics and `WIN`/`LOSS`/`DRAW` terminology.
2. `docs/normal-form.md` — binary conjugated form.
3. Sections 14--17 of `docs/verified-results.md` — constant-tail source
   coordinates and the original exponent-one obstruction.
4. Sections 79--81 — universal consecutive-factor coupling and the repaired
   two-level normalization.
5. Sections 87--90 — note carefully that the first-factor hidden parent of
   Section 89 has an additional typed congruence hypothesis.
6. Sections 91--135 — the typed obligation/factor normalizer and provenance
   machinery.
7. Corrected Sections 136--138 — retained-anchor versus routing-cursor
   distinction, the repaired arithmetic entry, and the explicit remaining
   attachment lemma.

## 7. Decisive manual obligations

Try to falsify these points first:

- the universal two-level normalization in corrected Section 137 really
  follows from Sections 79--81 for arbitrary `k>0`;
- no step confuses a decrease of canonical coefficient with a decrease of
  coefficient source;
- no transition silently promotes a temporary returned source `t` to the
  retained numerical anchor;
- Section 89 is used only when its congruence hypothesis has actually been
  proved by the constructor of the typed frame;
- every token-changing edge replaces an actual carried finite token by
  certified lower descendants;
- the typed Section 136 normalizer is well-founded without treating
  intermediate `A(x)` cursor growth as source descent;
- any future proof of the arbitrary exponent-one attachment lemma follows an
  actual outcome-compatible DRAW continuation.

## 8. Machine-checkable status

- Conjugated arithmetic and local identities: **PROVED / finite-regression supported** as stated in their sections.
- Symbolic typed routing assembly: **CONDITIONAL MACHINE CHECK**.
- Python finite checks: **COMPUTATIONALLY VERIFIED** at their stated limits.
- Lean metatheory subset: **KERNEL-CHECKED BUILD** at the scope in `formal/COVERAGE.md`.
- Arbitrary factorful exponent-one arithmetic normalization: **PROVED** in corrected Section 137.
- Arbitrary exponent-one provenance/rank attachment: **OPEN**.
- Global no-`DRAW` theorem: **OPEN IN THIS MANUSCRIPT**.
- Independent external acceptance: **PENDING**.

## 9. How to report a problem or completion

A useful report should identify the smallest precise item:

- exact section and statement;
- assumptions available at that point;
- counterexample, failed inference, or missing case;
- whether the issue is arithmetic, outcome compatibility, provenance, or
  global rank assembly.

For a proposed completion of the remaining attachment lemma, the crucial
question is not merely whether the returned factor/source can be computed,
but whether the old retained source/token projection is preserved or
strictly decreased on every outcome-compatible branch.
