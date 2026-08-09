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

The previous paragraph can be strengthened before the returned source `t`
is used. Suppose

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
  - If `q` is nonexceptional, the ordinary side relation makes
    `C_k=B(A(q))` a child of `ell`; hence `C_k` is WIN with
    `h(C_k)<=h(q)-2`. Since `R_k` is DRAW, its other child `T_k` is DRAW.
    The odd coefficient of `T_k` is not divisible by three, so `T_k` is a
    factor-free DRAW exit accompanied by a strict finite-token descent.
  - If `q` is exceptional, Section 68 applies exactly to
    `q WIN`, `A(q)=R_k DRAW`, `B(q)=ell LOSS`. It identifies
    `{C_k,T_k}` as an adjacent factor-free pair over the actual LOSS token
    `ell`, and at least one member is DRAW.

Therefore

\[
\boxed{
\begin{minipage}{0.88\linewidth}
Every factorful exponent-one DRAW reaches either a factor-free DRAW over the
same source, or a factor-free DRAW lift/frame while a certified finite
WIN/LOSS token strictly decreases. The unbounded factor exponent itself is
not a remaining obstruction.
\end{minipage}}
\]

This is now part of corrected Section 137.

## What remains after the stronger reduction

The remaining difficulty is a **factor-free base-entry attachment**, not an
arbitrary-`k` problem. A factor-free DRAW at exponent one is already handled
by the source-lift analysis of Sections 17--27. The delicate base case is an
exponent-two factor-free DRAW whose common contracting child has source below
`s` and is therefore WIN, while its expanding child enters the first
factor-one level.

The exact blocking statement is still phrased conservatively as the
**arbitrary exponent-one attachment lemma** in corrected Section 137, but the
new predecessor reduction proves that any completion only has to close this
factor-free first-entry geometry. It no longer has to control an unbounded
factor counter.

A useful local split for that base geometry is the following. Put

\[
a=J(s),\qquad
P=Q_1^\epsilon(a),\qquad U=Q_2^\epsilon(a).
\]

If `U` is DRAW, its common child with `P` has source below `s`, hence is WIN,
and `A(U)=Q_1^\epsilon(3a)` is DRAW. There are three possibilities for `P`:

1. `P` DRAW — this is already the factor-free exponent-one source-lift
   analysis; the B-selecting phase strictly returns below `s`, while the
   A-selecting phase is the canonical obligation.
2. `P` WIN — its other child is an actual LOSS token, while `U` and
   `A(U)` are DRAW. This has the local outcome geometry of the typed factor
   fork, but the entry must be connected to the retained rank without
   silently assuming the extra parent appearing in the definition of `O`.
3. `P` LOSS — both children of `P` are WIN while `U` and `A(U)` are DRAW.
   This is the sharpest remaining orientation. When the Section 89
   congruence fails, the factor-free pair `{U,P}` has the complementary
   exact parent
   \[
   K'=\frac{8a-1-\epsilon}{3},\qquad
   \operatorname{moves}(K')=\{U,P\},
   \]
   because in exactly those rows `U` lies in the image of `A` and
   `R(U)=P`. Thus this orientation already exposes an additional exact
   finite-height boundary relation. The complementary rows are the ones in
   which Section 89 supplies its own hidden parent to the exponent-three/two
   frame. A complete proof must join these two parent geometries to the
   existing token normalizer without a reset.

The last paragraph is a narrowing of the research target, not yet a global
closure lemma.

## Why the old global proof still cannot simply be restored

A returned arithmetic source is not guaranteed to lie below the old globally
minimal DRAW source. Therefore the proof may not replace the retained rank
anchor merely because a new source is the current routing cursor. Doing that
would reproduce the audited error in a different notation.

Corrected Section 136 consequently separates **retained anchors/tokens**
from temporary routing cursors. Its well-foundedness theorem is asserted only
for typed entries whose provenance has already been proved by Sections
91--135 or by a valid new entry lemma.

## Exact remaining lemma

> **Arbitrary exponent-one attachment lemma.** Assume `s` is the globally
> least coefficient source of a DRAW and
> \[
> Q_1^\epsilon(3^kJ(s))\text{ is DRAW},\qquad k>0.
> \]
> After the proved predecessor reduction, show that the resulting
> factor-free DRAW continuation can be connected to the retained outer rank
> so that an outcome-compatible finite continuation reaches at least one of:
>
> 1. an actual DRAW with retained coefficient source `<s`;
> 2. a certified strict replacement of an already carried finite proof
>    token, at retained source `s`;
> 3. a typed Section 136 normalizer entry with the old retained source/token
>    projection unchanged.
>
> A temporary routing source may not replace the retained source anchor
> without a proved strict comparison.

For `s>0`, the ordinary state `s` itself is finite (`WIN` or `LOSS`), because
its own coefficient source is at most `(s-1)/6<s`. Sections 54, 57, and
61--64, together with the new predecessor lemma, provide the main finite
proof-tree machinery for the remaining base attachment. Source zero has the
separate exact treatment of Sections 71--73.

## Current status

- old false Section 137 source-descent statement: **withdrawn**;
- arbitrary factorful exponent-one arithmetic case split: **repaired / proved**;
- unbounded factor-level obstruction: **removed by the predecessor reduction**;
- distinction between retained anchor and routing cursor: **made explicit**;
- typed normalizer after a valid entry: **retained**;
- factor-free base-entry provenance/rank attachment: **open**;
- global no-DRAW theorem: **open in the manuscript pending that lemma**.

The purpose of this branch is to make the repository safe to audit: no
machine result or local lemma is presented as closing the missing semantic
attachment step.
