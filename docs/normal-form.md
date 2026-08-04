# Exact binary normal form

This document records the most useful exact reduction currently known.

## Step 1: write the odd state as n=2m+1

Let

\[
n=2m+1,\qquad m\ge0.
\]

Define

\[
F(m)=\left\lceil\frac{3m}{2}\right\rceil.
\]

Let `R(m)` be obtained by deleting the maximal alternating suffix of the binary expansion of `m`.

Examples:

\[
1001_2\mapsto10_2,
\qquad
10101_2\mapsto0.
\]

For `m>0`, the two children in `m`-coordinates are exactly

\[
\boxed{F(m),\qquad F(R(m)).}
\]

### Direct verification of the first child

Since

\[
3n-1=2(3m+1),\qquad 3n+1=2(3m+2),
\]

exactly one of `3m+1` and `3m+2` is odd.

- If `m=2a`, the odd expression is `3m+1=6a+1`, which maps to `3a=F(m)`.
- If `m=2a+1`, the odd expression is `3m+2=6a+5`, which maps to `3a+2=F(m)`.

The extra divisions by two in the other branch are encoded by deleting the maximal alternating binary suffix. The identity is exhaustively tested by `scripts/verify_claims.py` and proved recursively by the four parity cases for `m` and its prefix.

## Step 2: conjugate by the injective map F

Every child in the preceding form lies in the image of `F`. Represent a state `F(q)` by `q`. The game becomes

\[
\boxed{
A(q)=F(q)=\left\lceil\frac{3q}{2}\right\rceil,
\qquad
B(q)=R(F(q)).
}
\]

The terminal state is `q=0`.

For every `q>0`,

\[
B(q)<q.
\]

Indeed, deleting a nonempty binary suffix gives

\[
B(q)\le \left\lfloor\frac{F(q)}2\right\rfloor
\le \left\lfloor\frac{3q+1}{4}\right\rfloor<q
\]

for `q>=2`, while `B(1)=0` directly.

Thus the conjugated graph has one expanding branch and one strictly contracting branch.

## Inverse of F

The image of `F` consists exactly of nonnegative integers not congruent to `1 mod 3`:

\[
F^{-1}(y)=
\begin{cases}
2y/3,&y\equiv0\pmod3,\\
(2y-1)/3,&y\equiv2\pmod3.
\end{cases}
\]

There is no preimage when `y` is congruent to `1 mod 3`.

## Arithmetic description of R

For `x>0`, the length of the alternating binary suffix can be read from a 2-adic valuation:

- if `x` is odd, its length is `v2(3x+1)`;
- if `x` is even, its length is `v2(3x+2)`.

Consequently,

\[
R(x)=
\begin{cases}
\left\lfloor x/2^{v_2(3x+1)}\right\rfloor,&x\text{ odd},\\
\left\lfloor x/2^{v_2(3x+2)}\right\rfloor,&x\text{ even}.
\end{cases}
\]

This identity should be independently formalized if it becomes central to a final proof.

## Why a fixed modulus is insufficient

For every fixed `K`, two integers can share the same residue modulo `2^K` while their alternating suffixes continue for different lengths beyond those `K` bits. Therefore no fixed residue `m mod 2^K` determines `R(m)` globally.

A successful finite-state argument must either read bits until the first repetition or supplement a suffix state with additional symbolic information.
