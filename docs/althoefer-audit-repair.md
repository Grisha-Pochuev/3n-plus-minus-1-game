# Althöfer audit repair — 9 August 2026

This note records the defect found by Ingo Althöfer and the conservative
repair that was made **before** the final attachment was closed.

**Historical status of this note:** its last `OPEN` conclusion has been
superseded on `repair/althoefer-audit-gap` by
[`althoefer-audit-closure.md`](althoefer-audit-closure.md), dated 10 August
2026.  The mathematical corrections recorded here remain part of the proof;
only the final status changed after the new one-shot attachment argument.

## Audit issue

The old Section 137 made two invalid moves.

1. It used a decrease of the canonical odd coefficient as a decrease of the
   coefficient **source**. Powers of three make this false. The explicit
   counterexample is
   \[
   s=1,\quad J(1)=5,\quad a=3J(1)=15,\quad \epsilon=1,
   \]
   with
   \[
   R(3a-\epsilon)=R(44)=22.
   \]
   The canonical coefficient is `11<15`, but `11=J(3)`, so the source
   increases from `1` to `3`.
2. It used Section 16 as if its reverse-factor lemma removed powers of three
   from constant-tail exponent one. Section 16 starts at exponent at least
   two. Therefore
   \[
   Q_1^\epsilon(3^kJ(s)),\qquad k>0,
   \]
   required a separate entry normalization.

Both shortcuts remain withdrawn after the final closure.

## First repair: universal two-level arithmetic normalization

Sections 79--81 are universal. Put

\[
a=J(s),\qquad
P_k=Q_2^\epsilon(3^ka),\qquad
R_k=Q_1^\epsilon(3^ka).
\]

If `R_k` is DRAW, Section 80 exposes a DRAW among the raw/signed exits at the
current or next factor level. At either exposed level factor

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
For `v=1`, the signed state is a factor-free exponent-one lift; a positive
raw DRAW has strict source `rho(C_i)<t`.

This is the complete arithmetic normalization of the omitted family. It
never asserts `t<s`.

## Second repair: predecessor reduction

Suppose

\[
R_k=Q_1^\epsilon(3^kJ(s))\text{ is DRAW},\qquad k\ge1.
\]

Section 87 gives either a factor-free DRAW over the original source `s`, or
the gate

\[
P_k\text{ LOSS},\qquad R_k\text{ DRAW}.
\]

In the gate take

\[
q=P_{k-1}=Q_2^\epsilon(3^{k-1}J(s)).
\]

Its children are

\[
A(q)=R_k,\qquad B(q)=C_{k-1}.
\]

Because `R_k` is DRAW, `q` is not LOSS.

- If `q` is DRAW, `k=1` is factor-free; for `k>1`, Section 16 may now be
  applied legitimately at exponent two to remove the factors of three.
- If `q` is WIN, `ell=C_{k-1}` is its unique LOSS child. If `q` is
  nonexceptional, `C_k=B(A(q))` is a WIN child of `ell` and has height at
  least two below `q`; `T_k` is forced DRAW. If `q` is exceptional, Section
  68 gives an adjacent factor-free DRAW frame over the actual LOSS token
  `ell`.

Thus the factor exponent cannot serve as an unmarked infinite escape.

## Third repair: exact base-boundary anchor

For any positive odd `a` and phase `e`, put

\[
P=Q_1^e(a),\qquad U=Q_2^e(a),\qquad
b=B(P)=B(U),\qquad F=A(U)=Q_1^e(3a).
\]

The exact first-factor identity is

\[
\boxed{9a+1-2e=2^vJ(b)},
\]

hence

\[
\boxed{A(F)=Q_v^{1-e}(J(b)).}
\]

The proof uses Sections 14 and 18. For `e=0`,

\[
\operatorname{oddpart}(9a+1)=J(R(3a))=J(b).
\]

For `e=1`,

\[
\operatorname{oddpart}(9a-1)=J(R(6a-1))=J(R(3a-1))=J(b).
\]

At a globally minimum DRAW source, with `a=J(s)` and `U` DRAW, Section 15
makes the common child `b` finite; because it is a child of a DRAW it is
WIN. The other child `F` is DRAW. Therefore the first factor exit is anchored
exactly at the already exposed WIN endpoint `b`, not at an unrelated source.

This identity is regression-supported by `tests/test_althoefer_repair.py`.

## Why this note originally stopped at OPEN

At this stage the returned inner arithmetic source could still exceed the
old retained source.  The conservative 9 August repair therefore refused to
promote it to the retained rank and isolated a **factor-free base-entry
attachment lemma**.  That was the correct thing to do: the old false
coefficient/source shortcut could not simply be replaced by another implicit
reset.

The remaining base geometry was

\[
a=J(s),\qquad P=Q_1^\epsilon(a),\qquad U=Q_2^\epsilon(a),
\]

with `U` DRAW, common child `b` WIN, and `F=A(U)` DRAW.

## 10 August closure

The missing step is now supplied by
[`althoefer-audit-closure.md`](althoefer-audit-closure.md). The new argument
adds two ingredients that were not present in this conservative note:

1. an exact phase/valuation split of the factor-free exponent-two base:
   B-selecting input gives `v=1`, while A-selecting input gives `v>=2`, with
   `v>=4` a strict source return, `v=2` an obligation, and `v=3` a typed frame
   whose constructor automatically proves the Section 89 congruence;
2. a one-shot entry component `eta`, placed after the outer source/token rank,
   that permits arbitrary finite **initialization** of the inner source while
   forbidding a same-fibre **reinitialization** unless an earlier source/token
   component has strictly decreased.

The closure therefore proves the attachment lemma without ever proving or
assuming `t<s`.

## Current status

- old false Section 137 source-descent statement: **WITHDRAWN**;
- invalid exponent-one use of Section 16: **WITHDRAWN**;
- arbitrary factorful exponent-one arithmetic normalization: **PROVED**;
- predecessor/token normalization: **PROVED**;
- exact first-factor returned source `J(b)`: **PROVED**;
- factor-free base-entry attachment: **PROVED IN THE 10 AUGUST CLOSURE ADDENDUM**;
- one-shot initialization/reset distinction: **PROVED IN THE CLOSURE ADDENDUM**;
- global no-DRAW theorem: **HUMAN-PROOF CLAIM RESTORED**;
- independent re-audit: **PENDING**;
- end-to-end Lean proof: **NOT CLAIMED**.
