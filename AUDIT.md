# Independent audit guide

This document tells a third party exactly what is currently claimed, what can
be checked mechanically, and where human review is still required after the
Althöfer audit and the 10 August closure addendum.

## 1. Current claim status

**GLOBAL THEOREM: HUMAN-PROOF CLAIM RESTORED; INDEPENDENT RE-AUDIT PENDING.**

The theorem is that every odd positive starting value in the two-player
`3n±1` game has finite remoteness, equivalently that the conjugated game has
no `DRAW` positions and optimal play reaches `1`.

The history is important.

1. The earlier manuscript claimed the theorem proved.
2. Ingo Althöfer's independent audit found a genuine entry gap in old Section
   137.
3. Corrected Sections 136--138 withdrew the invalid inference and deliberately
   recorded the theorem as open.
4. [`docs/althoefer-audit-closure.md`](docs/althoefer-audit-closure.md) now
   supplies the missing attachment lemma and restores the human-proof claim.

The closure addendum supersedes the `OPEN` conclusion at the end of corrected
Sections 137--138 on this repair branch. It does not alter the narrower scope
of the symbolic certificate or Lean project.

## 2. The audited defect remains withdrawn

The old Section 137 inferred a decrease of the coefficient **source** from a
decrease of the canonical odd coefficient. This is false in the presence of
powers of three. A concrete counterexample is

\[
s=1,\quad J(1)=5,\quad a=3J(1)=15,\quad \epsilon=1,
\]

for which

\[
R(3a-\epsilon)=R(44)=22.
\]

The new canonical coefficient is `11<15`, but `11=J(3)`, so the new source is
`3>1`.

The old proof also used Section 16 as though it removed powers of three at
constant-tail exponent one. It does not. Thus

\[
Q_1^\epsilon(3^kJ(s)),\qquad k>0,
\]

required a separate normalization.

Neither invalid step is used by the closure.

## 3. What corrected Section 137 established

Sections 79--81 give the universal two-level factor normalization. Writing

\[
3^{i+1}J(s)+1-2\epsilon=2^vJ(t)
\]

gives the exact signed exit

\[
Q_v^{1-\epsilon}(J(t)),
\]

and for `v>=2` the raw sibling

\[
Q_{v-1}^{1-\epsilon}(J(t)).
\]

For `v=1`, a positive raw DRAW has strict coefficient-source descent relative
to `t`.

Corrected Section 137 also proves the predecessor reduction: an arbitrary
factorful exponent-one DRAW either returns to a factor-free DRAW over the same
source or reaches a factor-free DRAW lift/frame with actual finite WIN/LOSS
provenance. Finally it proves the exact factor-free base identity

\[
9J(x)+1-2e=2^vJ(b),
\qquad
b=B(Q_1^e(J(x)))=B(Q_2^e(J(x))).
\]

These results are retained exactly as stated. They do **not** assert that a
returned source `t` is below the old source.

## 4. What the closure addendum adds

The missing bridge has two pieces.

### 4.1 Exact factor-free exponent-two base split

For a factor-free exponent-two DRAW with common WIN child `b`:

- if the input phase is B-selecting, the next factor valuation is exactly
  `v=1`; the raw exit is an actual ordinary child of `b`;
- if that raw ordinary child is DRAW, either the ordinary/exceptional side
  diamond supplies a strict finite proof-token edge, or the sole exceptional
  B-child row has a strict source estimate;
- if the input phase is A-selecting, `v>=2`;
- `v>=4` implies `b<x`, hence a strict source exit;
- `v=2` is exactly an obligation `O(b,1-e)`;
- `v=3` automatically satisfies the additional congruence required by
  Section 89, so Sections 87--90 apply legitimately.

The proof is in `docs/althoefer-audit-closure.md`. The finite regression in
`tests/test_althoefer_closure.py` checks the corresponding identities over a
large finite prefix but is not the proof.

### 4.2 One-shot initialization versus reset

The returned inner source can be larger than the outer retained source. The
closure does not try to forbid this. Instead it inserts an entry component

\[
\eta\in\{1,0\},\qquad1>0,
\]

after the outer source and outer proof-token multiset.

`eta=1 -> 0` is a strict transition and may initialize arbitrary finite inner
routing data. Once `eta=0`, the same outer source/token fibre cannot reset it
to `1`. A fresh raw entry is permitted only after an earlier outer source or
proof-token component has strictly decreased. This is a direct application of
the lexicographic/reset discipline behind Sections 129 and 132.

Therefore `t>s` on the **first inner initialization** is harmless, while an
unranked repeated source reset remains forbidden.

## 5. Trust boundary

An audit has four separate layers.

| Layer | What it establishes | What it does not establish |
|---|---|---|
| Human proof, including the closure addendum | The global theorem if every cited local lemma and the new entry argument are correct | Kernel verification or independent acceptance |
| Symbolic routing certificate | The declared finite control/rank assembly for typed entries | The new one-shot semantic bridge from the original game |
| Python arithmetic and finite certificates | Exact implementation agreement on stated finite ranges and genuine finite `WIN`/`LOSS` proof DAGs | The infinite theorem by computation alone |
| Lean build | Definitions and metatheorems listed in `formal/COVERAGE.md` | The concrete entry bridge or the global no-`DRAW` theorem |

The symbolic checker may still print `CONDITIONAL_MACHINE_CHECK`. This remains
correct. The closure is a human proof layer above that typed certificate, not
a silent expansion of the checker's scope.

## 6. Reproducibility checks

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

This runs regression tests, finite arithmetic checks, finite outcome
certificates, and the declared symbolic routing checker. A successful result
supports the arithmetic/software layer but does **not** machine-prove the new
one-shot entry lemma.

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

## 7. Human proof audit order

Read the mathematics in this order:

1. `docs/problem.md` — game semantics and `WIN`/`LOSS`/`DRAW` terminology.
2. `docs/normal-form.md` — binary conjugated form.
3. Sections 14--17 of `docs/verified-results.md` — constant-tail/source
   coordinates and the original exponent-one obstruction.
4. Sections 79--81 — universal consecutive-factor coupling.
5. Sections 87--90 — especially the precise congruence hypothesis of Section
   89.
6. Sections 91--135 — typed obligation/factor normalizer and proof-token
   provenance.
7. Corrected Sections 136--138 — conservative post-audit repair ending with
   the attachment lemma still open.
8. `docs/althoefer-audit-closure.md` — the base phase/valuation split and
   one-shot entry proof that supersede that final open status.
9. `docs/global-proof.md` — concise final assembly.

## 8. Decisive hostile checks

Try to falsify these points first:

- B-selecting base phase really forces the *next* factor valuation to be
  exactly one;
- the raw state in that row is exactly an ordinary child of `b`, not merely a
  state with the same coefficient source;
- in the exceptional raw B-child row the displayed estimate really gives
  `rho(C)<x` for every positive input;
- A-selecting base phase really gives `v>=2`;
- the inequality `v>=4 => b<x` uses the correct `J` bounds and has no small
  exception;
- the valuation-three constructor really gives
  `J(b) congruent to 1+g mod 3`, so Section 89 is not used outside its
  hypothesis;
- `eta` never changes `0->1` inside an unchanged outer source/token fibre;
- every later reset follows an actual strict source or Section 129 token
  decrease;
- no finite endpoint of unrelated height is silently inserted into the
  retained multiset;
- every macrostep still follows an actual DRAW member while finite tokens are
  carried separately.

## 9. Status matrix

- Conjugated arithmetic and local identities: **PROVED / finite-regression supported** as stated.
- Arbitrary factorful exponent-one arithmetic normalization: **PROVED**.
- Predecessor/token normalization: **PROVED**.
- Exact first-factor anchor identity: **PROVED**.
- Factor-free exponent-two phase/valuation attachment: **PROVED IN CLOSURE ADDENDUM**.
- One-shot provenance/rank attachment: **PROVED IN CLOSURE ADDENDUM**.
- Arbitrary exponent-one attachment lemma: **PROVED IN CLOSURE ADDENDUM**.
- Global no-`DRAW` theorem: **HUMAN-PROOF CLAIM RESTORED**.
- Symbolic typed routing assembly: **CONDITIONAL MACHINE CHECK**.
- Python finite checks: **COMPUTATIONALLY VERIFIED** at their stated limits when reproduced.
- Lean metatheory subset: **KERNEL-CHECKED BUILD** at the scope in `formal/COVERAGE.md` when reproduced.
- End-to-end Lean proof: **NOT CLAIMED**.
- Independent external re-audit/acceptance: **PENDING**.

## 10. How to report a problem

A useful report should identify the smallest precise item:

- exact section/addendum statement;
- assumptions available at that point;
- a counterexample, failed inference, or missing outcome orientation;
- whether the issue is arithmetic, outcome compatibility, provenance, reset
  discipline, or final well-foundedness.

In particular, any proposed counterexample to the closure should distinguish
between a large *inner* source initialized on `eta:1->0` and an illegal
same-fibre reinitialization after `eta=0`; only the latter would invalidate the
rank argument.
