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

## Gray-code form of the suffix deletion

Let

\[
G(x)=x\mathbin{\mathtt{xor}}\left\lfloor\frac{x}{2}\right\rfloor
\]

be reflected binary Gray code.  Then the alternating-suffix operation has the
exact form

\[
\boxed{
G(R(x))=
\left\lfloor
\frac{G(x)}{2^{v_2(G(x)+1)+1}}
\right\rfloor
}
\qquad(x\ge0).
\]

To see this, write the binary digits of `x` as `b_i`.  Except at the leading
digit, the Gray digit in position `i` is `b_{i+1} xor b_i`.  If the maximal
alternating suffix has length `k` and a nonempty prefix remains, its lower
`k-1` Gray digits are `1`, while the boundary Gray digit is `0`.  Therefore
`v2(G(x)+1)=k-1`, and shifting Gray code right by `k` positions leaves exactly
the Gray code of the remaining prefix `R(x)`.

If the whole binary word is alternating, its Gray code is all ones.  The
displayed exponent is then one larger than the word length, but both sides of
the identity are still zero.  The case `x=0` is immediate.

Consequently, after conjugating once more by `G`, the two game moves are

\[
\Gamma(g)=G(A(G^{-1}(g))),
\qquad
P(\Gamma(g)),
\]

where

\[
P(h)=h\mathbin{\mathtt{>>}}(v_2(h+1)+1).
\]

Thus the unbounded alternating-suffix scan becomes the simple operation
"delete the terminal run of ones and the zero immediately to its left" in
Gray coordinates.  Multiplication by `3` and its carry state remain in
`Gamma`; this identity alone is not a rank proof.

## An eight-state transducer for Gamma

The remaining map `Gamma` is an exact finite-state relation.  Read the Gray
digits from least significant to most significant.  Write `b_i` for the
binary digits of `q`, `c_i` for those of `A(q)`, and use the identity

\[
2A(q)=3q+b_0.
\]

A state at position `i` is

\[
(b_i,c_i,d_{i+1})\in\{0,1\}^3,
\]

where `d` is the carry into column `i+1` of the addition `q+2q+b_0`.
If the next input and output Gray digits are `g_i` and `h_i`, put

\[
b_{i+1}=b_i\mathbin{\mathtt{xor}}g_i,
\qquad
c_{i+1}=c_i\mathbin{\mathtt{xor}}h_i.
\]

The transition is legal exactly when

\[
c_i\equiv b_{i+1}+b_i+d_{i+1}\pmod2,
\]

and its new carry is

\[
d_{i+2}=\left\lfloor
\frac{b_{i+1}+b_i+d_{i+1}}2
\right\rfloor.
\]

There are only eight possible states.  Initially `b_0` is guessed and the
carry is forced to equal it; `c_0` is also guessed.  After one leading-zero
padding column the accepting state is `(0,0,0)`.  The accepting condition
makes both guesses unique, because Gray digits together with a leading zero
uniquely reconstruct the binary digits.  Column-by-column addition then
proves that the accepted pairs are exactly

\[
\boxed{(G(q),G(A(q)))}.
\]

The complete transition predicate and an exhaustive functional regression
test are in `src/optimal_3n1/transducer.py` and `tests/test_game.py`.  Together
with the preceding suffix-deletion machine, both game edges are therefore
rational binary relations.  A well-founded game-theoretic rank is still
needed; finite-state representability alone does not exclude `DRAW`.
