# Althöfer audit repair — 9 August 2026

This note records the external audit issue, the correction already proved,
and the exact statement that still blocks the global theorem.

## Audit issue

The old Section 137 made two invalid moves.

1. It used a decrease of the canonical odd coefficient as a decrease of the
   coefficient **source**. Powers of three make this false. The smallest
   explicit example used in the repair is
   \[
   s=1,\quad J(1)=5,\quad a=3J(1)=15,\quad \epsilon=1,
   \]
   with common child
   \[
   R(3a-\epsilon)=R(44)=22.
   \]
   The new canonical coefficient is `11<15`, but `11=J(3)`, so the source
   increases from `1` to `3`.
2. It used the reverse factor lemma of Section 16 as if that lemma removed
   powers of three from constant-tail exponent one. Section 16 starts at
   exponent at least two. The arbitrary family
   \[
   Q_1^\epsilon(3^kJ(s)),\qquad k>0,
   \]
   therefore had no proved entry to the final normalizer.

## First repair: universal two-level arithmetic normalization

Sections 79--81 are universal and do apply to the missing family. Put

\[
a=J(s),\qquad
P_k=Q_2^\epsilon(3^ka),\qquad
R_k=Q_1^\epsilon(3^ka).
\]

If `R_k` is DRAW, the adjacent frame contains a DRAW. Section 80 gives a
DRAW among

\[
C_k,T_k,C_{k+1},T_{k+1},
\]

where `C_i=B(P_i)=B(R_i)` and `T_i=A(R_i)`.

At either exposed level factor

\[
3^{i+1}J(s)+1-2\epsilon=2^vJ(t).
\]

Then

\[
T_i=Q_v^{1-\epsilon}(J(t)).
\]

For `v>=2`, Section 81 gives

\[
C_i=Q_{v-1}^{1-\epsilon}(J(t)),
\]

so the raw/signed pair is an exact factor-free adjacent frame over `t`.
For `v=1`, the signed state is already an exponent-one factor-free lift; a
positive raw DRAW has strict source `rho(C_i)<t`.

This is an exact two-level normalization for arbitrary `k`; no bounded
factor search is used. It repairs the arithmetic omission but does not prove
`t<s`.

## Second repair: the predecessor removes the unbounded factor level

Suppose

\[
R_k=Q_1^\epsilon(3^kJ(s))\text{ is DRAW},\qquad k\ge1.
\]

Section 87 gives either a factor-free DRAW over the original source `s`, or
the gate

\[
P_k\text{ LOSS},\qquad R_k\text{ DRAW}.
\]

In the gate case take the exact predecessor one factor level lower,

\[
q=P_{k-1}=Q_2^\epsilon(3^{k-1}J(s)).
\]

Its children are

\[
A(q)=R_k,\qquad B(q)=C_{k-1}.
\]

Because `R_k` is DRAW, `q` is not LOSS.

- If `q` is DRAW, then for `k=1` it is already factor-free; for `k>1`,
  Section 16 may be iterated at exponent two and removes all powers of
  three. Thus a factor-free DRAW over the original source `s` is obtained.
- If `q` is WIN, then `ell=C_{k-1}=B(q)` is its unique LOSS child and
  `h(ell)=h(q)-1`.
  - If `q` is nonexceptional, `C_k=B(A(q))` is a child of `ell`; hence
    `C_k` is WIN with `h(C_k)<=h(q)-2`. Since `R_k` is DRAW, its other
    child `T_k` is DRAW and is factor-free.
  - If `q` is exceptional, Section 68 identifies `{C_k,T_k}` as an
    adjacent factor-free pair over the actual LOSS token `ell`, and at least
    one member is DRAW.

Therefore every factorful exponent-one DRAW reaches either a factor-free
DRAW over the same source, or a factor-free DRAW lift/frame while a certified
finite WIN/LOSS token strictly decreases. The unbounded factor exponent is
not a remaining obstruction.

## Third repair: the first factor exit is anchored at the old boundary WIN

The factor-free exponent-two base entry has an exact identity that removes
another apparent source reset. Let `a` be positive and odd, `e` be a phase,
and put

\[
P=Q_1^e(a),\qquad U=Q_2^e(a),\qquad
b=B(P)=B(U),\qquad F=A(U)=Q_1^e(3a).
\]

Then, for the exact valuation `v`,

\[
\boxed{9a+1-2e=2^vJ(b)}.
\]

Hence

\[
\boxed{A(F)=Q_v^{1-e}(J(b)).}
\]

This is proved from Sections 14 and 18, not guessed from computation. For
`e=0`, Section 18 applied to `w=3a` gives

\[
\operatorname{oddpart}(9a+1)=J(R(3a))=J(b).
\]

For `e=1`, the second identity of Section 18 gives

\[
\operatorname{oddpart}(9a-1)=J(R(6a-1)),
\]

and Section 14 gives `R(6a-1)=R(3a-1)=b`.

Now take `a=J(s)` and suppose the factor-free exponent-two state `U` is
DRAW at globally minimum DRAW source `s`. Its common child `b` has canonical
coefficient below `J(s)`, so its own coefficient source is strictly below
`s`; hence `b` is not DRAW. Since it is a child of `U`, it is not LOSS
either, and therefore

\[
\boxed{b\text{ is WIN}.}
\]

The other child `F` of `U` is DRAW. The exact factorization above says that
the first signed factor exit is not over a new arbitrary source: it is over
this already exposed finite WIN endpoint `b`. If `v>=2`, the two children of
`F` are the adjacent factor-free frame

\[
Q_v^{1-e}(J(b)),\qquad Q_{v-1}^{1-e}(J(b));
\]

if `v=1`, the signed child is the factor-free exponent-one lift over `b`,
and a positive DRAW raw exit has the strict Section 81 source decrease.

This identity is also regression-tested in `tests/test_althoefer_repair.py`
for the first 10,000 sources in both phases. The test is supporting evidence;
the proof is the two-case argument above.

## What remains after the stronger reductions

The remaining difficulty is no longer an arbitrary factor exponent and no
longer an arbitrary first returned source. It is now a **factor-free
base-entry attachment over an already carried finite WIN token**.

A factor-free DRAW at exponent one is handled by the source-lift analysis of
Sections 17--27. The delicate base case is an exponent-two factor-free DRAW
whose common contracting child `b` is a known WIN and whose expanding child
enters the factor-one scan anchored exactly at `b` by the identity above.

Put

\[
a=J(s),\qquad
P=Q_1^\epsilon(a),\qquad U=Q_2^\epsilon(a).
\]

If `U` is DRAW, there are three possible outcomes for `P`:

1. `P` DRAW — this is already the factor-free exponent-one source-lift
   analysis; the B-selecting phase strictly returns below `s`, while the
   A-selecting phase is the canonical obligation.
2. `P` WIN — because the common child is WIN, the other child of `P` is an
   actual LOSS token. Together with `U` DRAW and `A(U)` DRAW, this is the
   local outcome geometry used by the typed factor fork; the remaining audit
   question is to enter that subsystem without importing an unproved parent.
3. `P` LOSS — both children of `P` are WIN while `U` and `A(U)` are DRAW.
   This is the sharpest remaining orientation. When the Section 89
   congruence fails, `{U,P}` has the complementary exact parent
   \[
   K'=\frac{8a-1-\epsilon}{3},\qquad
   \operatorname{moves}(K')=\{U,P\}.
   \]
   In the complementary congruence rows, Section 89 supplies its hidden
   parent to the exponent-three/two frame. These two exact parent geometries
   are the remaining pieces that must be joined to the fixed-fibre token
   normalizer without an unranked reset.

## Why the old global proof still cannot simply be restored

A temporary arithmetic source is not automatically a new retained rank
anchor. Corrected Section 136 therefore separates **retained anchors/tokens**
from routing cursors. A source can replace a retained anchor only after a
proved strict comparison; a finite outcome can replace a proof token only
after a proved height comparison.

## Exact remaining lemma

> **Factor-free base-entry attachment lemma.** Let `s` be the globally least
> coefficient source of a DRAW. After the proved predecessor reduction has
> reduced any factorful exponent-one entry to the factor-free base geometry,
> and after the exact first-factor identity has exposed the finite WIN token
> `b`, prove that every outcome-compatible continuation either:
>
> 1. reaches an actual DRAW with retained source `<s`;
> 2. strictly replaces an already carried finite proof token;
> 3. enters a typed Section 136 normalizer state with the retained outer
>    source/token projection unchanged.
>
> In particular, a long adjacent factor-free frame over `b` must be
> normalized while `b` (or a certified descendant of it) remains marked.

For `s>0`, the ordinary state `s` itself is finite (`WIN` or `LOSS`) because
its coefficient source is at most `(s-1)/6<s`. Sections 54, 57, 61--64,
79--90, and 91--96 contain most of the local transition machinery needed for
this final attachment. Source zero has the separate exact treatment of
Sections 71--73.

## Current status

- old false Section 137 source-descent statement: **withdrawn**;
- arbitrary factorful exponent-one arithmetic case split: **repaired / proved**;
- unbounded factor-level obstruction: **removed by the predecessor reduction**;
- first factor returned source: **proved to equal the already exposed WIN endpoint `b`**;
- retained-anchor versus routing-cursor distinction: **made explicit**;
- typed normalizer after a valid entry: **retained**;
- factor-free base-entry provenance/rank attachment over the finite WIN token: **open**;
- global no-DRAW theorem: **open in the manuscript pending that lemma**.

The repair branch is intentionally conservative: no machine result or local
lemma is presented as closing the remaining semantic attachment step.
