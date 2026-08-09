# Althöfer audit repair — 9 August 2026

This note records the external audit issue, the correction already proved,
and the exact statement that still blocks the global theorem.

## Audit issue

The old Section 137 made two invalid moves.

1. It used a decrease of the canonical odd coefficient as a decrease of the
   coefficient **source**.  Powers of three make this false.  The smallest
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
   powers of three from constant-tail exponent one.  Section 16 starts at
   exponent at least two.  The arbitrary family
   \[
   Q_1^\epsilon(3^kJ(s)),\qquad k>0,
   \]
   therefore had no proved entry to the final normalizer.

## Arithmetic repair now proved

Sections 79--81 are universal and do apply to the missing family.  Put

\[
a=J(s),\qquad
P_k=Q_2^\epsilon(3^ka),\qquad
R_k=Q_1^\epsilon(3^ka).
\]

If `R_k` is DRAW, the adjacent frame contains a DRAW.  Section 80 gives a
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
factor search is used.

## Why this is not yet the global proof

The returned source `t` is not guaranteed to be below the old globally
minimal DRAW source `s`.  Therefore the proof may not replace the retained
rank anchor `s` by `t` merely because `t` is the current routing source.
Doing that would reproduce the audited error in a different notation.

Corrected Section 136 consequently separates **retained anchors/tokens**
from temporary routing cursors.  Its well-foundedness theorem is asserted
only for typed entries whose provenance has already been proved by Sections
91--135.

## Exact remaining lemma

> **Arbitrary exponent-one attachment lemma.** Assume `s` is the globally
> least coefficient source of a DRAW and
> \[
> Q_1^\epsilon(3^kJ(s))\text{ is DRAW},\qquad k>0.
> \]
> Starting from the universal two-level normalization above, prove that an
> outcome-compatible finite continuation reaches at least one of:
> 
> 1. an actual DRAW with retained coefficient source `<s`;
> 2. a certified strict replacement of an already carried finite proof
>    token, at retained source `s`;
> 3. a typed Section 136 normalizer entry with the old retained source/token
>    projection unchanged.
>
> A returned arithmetic source `t` may be routing data, but may not replace
> the retained source anchor without a proved strict comparison.

For `s>0`, the ordinary state `s` itself is finite (`WIN` or `LOSS`), because
its own coefficient source is at most `(s-1)/6<s`.  Thus Sections 54, 57,
and 61--64 provide genuine finite proof-tree data that may be useful in the
remaining attachment proof.  Source zero has the separate exact treatment
of Sections 71--73.

## Current status

- old false Section 137 source-descent statement: **withdrawn**;
- arbitrary factorful exponent-one arithmetic case split: **repaired / proved**;
- distinction between retained anchor and routing cursor: **made explicit**;
- typed normalizer after a valid entry: **retained**;
- arbitrary exponent-one provenance/rank attachment: **open**;
- global no-DRAW theorem: **open in the manuscript pending that lemma**.

The purpose of this branch is to make the repository safe to audit: no
machine result or local lemma is presented as closing the missing semantic
attachment step.
