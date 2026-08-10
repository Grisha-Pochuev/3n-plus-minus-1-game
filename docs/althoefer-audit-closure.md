# Althöfer audit closure addendum — 10 August 2026

Status: **HUMAN-PROOF REPAIR SUPPLIED; INDEPENDENT RE-AUDIT PENDING.**

This addendum closes the entry defect isolated by the 9 August repair note.
It is deliberately separate from the historical text of corrected Sections
136--138 so that an auditor can see exactly which new statements restore the
final implication.  It supersedes the `OPEN` conclusion at the end of those
sections on the branch `repair/althoefer-audit-gap`.

The two statements withdrawn after Ingo Althöfer's audit remain withdrawn:

1. a smaller canonical coefficient is **not** automatically a smaller
   coefficient source when powers of three are present;
2. Section 16 does **not** remove powers of three from exponent one.

No part of the closure below reinstates either shortcut.

## 1. Previously proved repair ingredients

Use the notation of `docs/verified-results.md`.

For a positive odd coefficient `a`, phase `e in {0,1}`, and tail exponent
`r>=1`,

\[
Q_r^e(a)=a2^r-e.
\]

Every odd coefficient has a unique form `3^k J(s)`, where `J(s)` is
three-free.  Sections 79--81 prove the universal two-level factor scan.  If

\[
R_k=Q_1^e(3^kJ(s))
\]

is DRAW, then one of the current or next raw/signed exits is DRAW.  At either
exposed level, writing

\[
3^{i+1}J(s)+1-2e=2^vJ(t)
\]

gives

\[
T_i=Q_v^{1-e}(J(t)),
\]

and for `v>=2`,

\[
C_i=Q_{v-1}^{1-e}(J(t)).
\]

For `v=1`, a positive raw DRAW has strict coefficient-source descent relative
to `t`.  This part is independent of any comparison between `t` and `s`.

The predecessor repair in corrected Section 137 is also retained.  For
`k>=1`, if the factor frame does not pull back to a factor-free DRAW over the
same source, its sole gate has

\[
P_k\text{ LOSS},\qquad R_k\text{ DRAW}.
\]

The exact predecessor

\[
q=P_{k-1}=Q_2^e(3^{k-1}J(s))
\]

is not LOSS.  If it is WIN, its other child is an actual LOSS proof token;
the nonexceptional side gives a lower WIN descendant, while the exceptional
side gives the exact adjacent frame of Section 68 over that LOSS token.  Thus
an arbitrary exponent-one factor power cannot create an unmarked reset.

Finally, the exact base-boundary identity proved in corrected Section 137 is

\[
\boxed{9a+1-2e=2^vJ(b)},
\qquad
b=B(Q_1^e(a))=B(Q_2^e(a)).
\]

Consequently the first signed factor exit from
`F=A(Q_2^e(a))=Q_1^e(3a)` is anchored exactly at `b`.

## 2. The missing rank idea: one-shot initialization

The returned arithmetic source `t` may exceed the globally retained source
`s`.  The old proof tried to rule this out.  That was unnecessary.

There are two logically different operations:

- **initializing** the typed normalizer after a raw entry has been reduced;
- **resetting** a normalizer that is already running.

Only the second operation needs a preceding strict source/token decrease.
The first happens once in a fixed retained outer fibre.

Formally, refine the marked rank by an entry bit

\[
\eta\in\{1,0\},
\]

ordered by `1>0`.  The retained rank is the lexicographic product

\[
(\text{outer source},\ \Phi(M),\ \eta,\
  \text{inner source/token rank},\ \text{finite control rank}).
\]

Here `Phi(M)` is the proof-token multiset rank of Section 129.

- `eta=1` means that the current outer source/token fibre has not yet
  initialized its typed inner normalizer.
- `eta=0` means that the typed Section 136 normalizer is running.

The transition

\[
\boxed{\eta:1\longrightarrow0}
\]

is strict independently of the numerical value chosen for the newly
initialized inner source.  Therefore the first returned source may be
`t>s`; it is installed **after** the strict entry-bit component.

Within a fixed outer source/token fibre, `eta` never returns from `0` to `1`.
A later reset to a fresh raw-entry state is permitted only after an earlier
outer source or outer proof-token component has strictly decreased.  This is
exactly the reset discipline of the well-founded-fibre lemma in Section 132.
Thus the entry bit cannot oscillate and cannot be used to hide repeated source
growth.

This is the precise replacement for the false inference `t<s`.

## 3. Universal factor-free exponent-two bootstrap

It remains to prove that a factor-free exponent-two DRAW has a legitimate
one-shot entry.  Let `x>0`, put

\[
a=J(x),\qquad
P=Q_1^e(a),\qquad U=Q_2^e(a),
\]

\[
b=B(P)=B(U),\qquad F=A(U)=Q_1^e(3a),\qquad g=1-e.
\]

Assume `U` is DRAW and, at the globally minimum outer source, use Section 15
to exclude a DRAW at the common child.  Hence

\[
\boxed{b\text{ WIN},\qquad F\text{ DRAW}.}
\]

The outcome of `P` is irrelevant for the following split.

### 3.1 B-selecting input phase

Suppose

\[
e=1-\alpha(x).
\]

The source-boundary transition at `x` is B-selecting, so
`e=A(x) mod 2`.  Writing `u=A(x)` and using `J(x)=2u+1`, direct binary
substitution gives

\[
\boxed{b=3A(x)+1}.
\]

Indeed,

\[
A(P)=3J(x)-e=6u+3-e,
\]

and because `u mod 2=e`, the last appended bit repeats the previous bit;
the maximal alternating suffix has length one and its deletion leaves
`3u+1`.

Now compare consecutive signed numerators.  The B-selecting numerator at the
first source boundary is divisible by four.  Therefore

\[
9J(x)+1-2e
=3(3J(x)+1-2e)-2(1-2e)
\equiv2\pmod4.
\]

Hence the base-factor valuation is exactly

\[
\boxed{v=1}.
\]

The two children of the DRAW state `F` are therefore

\[
T=Q_1^g(J(b)),\qquad C=R(T).
\]

Section 119's signed-prefix identity identifies the raw child exactly:

\[
\boxed{C\in\{A(b),B(b)\},}
\]

namely the ordinary child of `b` selected by phase `g`.

At least one of `T,C` is DRAW.

- If `T` is DRAW, this is the first alternative of the exact obligation
  `O(b,g)`.  The one-shot entry initializes the typed normalizer at `b`.
- If `C` is DRAW, then the other ordinary child `ell` of the WIN state `b`
  is LOSS.  If `b` is nonexceptional, the ordinary common-child identity
  makes `B(A(b))` a WIN child of `ell` and a child of the DRAW state `C`;
  this is a strict proof-token/boundary descent.  If `b` is exceptional and
  `C=A(b)`, Section 68 gives an adjacent DRAW frame over the actual LOSS
  token `ell`, again a strict token attachment.

The only exceptional orientation not covered by Section 68 is
`C=B(b)` DRAW.  It is a strict source return.  Since `b=3A(x)+1`,

\[
b\le\frac{9x+5}{2}.
\]

For exceptional `b`, the alternating suffix of `A(b)` has length at least
three, so

\[
C=B(b)\le\frac{A(b)}8\le\frac{3b+1}{16}.
\]

If `rho(C)` is its coefficient source, then

\[
\rho(C)<\frac C6
\le\frac{3b+1}{96}
\le\frac{27x+17}{192}<x.
\]

Thus this last row is a genuine strict retained-source transition (and is
impossible when `x` is the globally minimum DRAW source).

Therefore **every B-selecting exponent-two base entry is attached**: it
enters a typed obligation, spends a finite proof token, or strictly lowers
the source.

### 3.2 A-selecting input phase

Suppose instead

\[
e=\alpha(x).
\]

Section 17 gives

\[
3J(x)+1-2e=2J(A(x)),
\]

so the first source-boundary valuation is exactly one.  The consecutive
numerator identity then implies

\[
\boxed{v_2(9J(x)+1-2e)\ge2.}
\]

Retain

\[
9J(x)+1-2e=2^vJ(b).
\]

If `v>=4`, then

\[
16J(b)\le9J(x)+1\le27x+19.
\]

Using `J(b)>=3b+1` gives

\[
48b+16\le27x+19,
\qquad
\boxed{b\le\frac{9x+1}{16}<x}.
\]

Since `F` is DRAW and both of its children have the factor-free source `b`,
this is a strict source exit.  At a globally minimum source it is impossible.

Only `v=2,3` remain without an immediate source decrease.

- `v=2`: `F` is a DRAW parent whose children are exactly
  \[
  Q_2^g(J(b)),\qquad Q_1^g(J(b)).
  \]
  Hence the second alternative of `O(b,g)` holds and the typed normalizer is
  entered directly.
- `v=3`: the children are the exact valuation-three frame
  \[
  Q_3^g(J(b)),\qquad Q_2^g(J(b)).
  \]
  The constructor automatically supplies the Section 89 congruence.  Indeed,
  reducing
  \[
  9J(x)+1-2e=8J(b)
  \]
  modulo three and using `g=1-e` gives
  \[
  \boxed{J(b)\equiv1+g\pmod3.}
  \]
  Thus Section 89 is being used only under its proved hypothesis.  Sections
  87--90 then give exactly a strict source edge, a strict boundary/token edge,
  or the already typed obligation entry.

Therefore **every A-selecting exponent-two base entry is attached** as well.

The source-zero base is unchanged and remains covered by Sections 71--73.

## 4. Closure of the arbitrary factorful exponent-one family

Return to

\[
Q_1^e(3^kJ(s))\text{ DRAW},\qquad k>0.
\]

The predecessor reduction from corrected Section 137 has two outputs.

1. It returns to a factor-free DRAW over the same source.  The ordinary
   factor-free entry analysis now terminates at exponent one (an exact
   obligation) or exponent two, and the exponent-two bootstrap of Section 3
   above supplies the previously missing attachment.
2. It exposes a factor-free DRAW lift/frame together with an actual finite
   WIN/LOSS descendant of the exact predecessor token.  This is already a
   certified token edge of the Section 129 multiset order.  Section 132
   therefore permits the inner arithmetic/factor task to reset.  The new
   arithmetic source is then routing/inner data; it is not substituted for
   the retained outer source.

This proves the missing statement without ever asserting `t<s`:

\[
\boxed{
\begin{minipage}{0.88\linewidth}
Every arbitrary factorful exponent-one DRAW has a finite outcome-compatible
normalization that either strictly lowers the retained source, strictly lowers
an already marked finite proof token, or consumes the one-shot entry bit and
enters the typed Section 136 normalizer.
\end{minipage}}
\]

That is exactly the attachment lemma isolated after the Althöfer audit.

## 5. Why the entry bit cannot hide a cycle

The entry component is placed **after** the outer source and outer proof-token
multiset.  Consequently:

- a strict outer source edge may reset the token multiset, entry bit, and all
  inner data;
- at fixed outer source, a strict Section 129 token replacement may reset the
  entry bit and all inner data;
- with both outer components fixed, `eta=1 -> 0` may initialize arbitrary
  finite inner source/token data once;
- with `eta=0`, the route is entirely inside the typed Section 136 relation
  and cannot return to `eta=1` unless an earlier outer component has already
  decreased.

Thus a route cannot alternate indefinitely between arbitrary raw entries and
large returned sources.  Either an earlier lexicographic component falls, or
one fixed typed fibre is eventually reached.  Section 132 and the corrected
Section 136 then give well-foundedness.

## 6. Restored final implication

Assume a DRAW exists and choose the least coefficient source `s` of a DRAW.
The source-zero case is covered by Sections 71--73.  For `s>0`, the corrected
constant-tail/predecessor analysis plus Sections 3--4 above gives a marked
macro-configuration containing an actual DRAW and one of three transitions:

1. a retained-source decrease;
2. a strict Section 129 proof-token replacement;
3. a one-shot entry into the typed Section 136 normalizer.

The first contradicts minimality when it occurs at the initial outer source.
More generally it is a strict first lexicographic component.  The second is
well-founded by Section 129.  The third strictly consumes the entry bit and
then remains in a well-founded Section 136 fibre.  By Section 132 the complete
marked relation is well-founded.

But every DRAW has no LOSS child and has at least one DRAW child.  Repeating
the finite outcome-compatible macro-normalization would therefore produce an
infinite marked route, contradicting that well-foundedness.  Hence

\[
\boxed{\text{the conjugated game has no DRAW positions}.}
\]

The conjugacy then gives finite optimal play to original state `1` from every
odd positive starting value, as in the former final Section 138.

## 7. Audit status after this addendum

- false coefficient-to-source implication: **WITHDRAWN, not used**;
- exponent-one use of Section 16: **WITHDRAWN, not used**;
- universal two-level factor arithmetic: **PROVED** (Sections 79--81);
- arbitrary factor-level predecessor reduction: **PROVED** (corrected §137);
- exact first-factor anchor identity: **PROVED** (corrected §137);
- B-selecting base valuation-one attachment: **PROVED in this addendum**;
- A-selecting base valuation `2/3/>=4` split: **PROVED in this addendum**;
- Section 89 hypothesis at the valuation-three entry: **PROVED automatically by the constructor**;
- one-shot entry/reset distinction: **PROVED order-theoretically in this addendum**;
- arbitrary exponent-one attachment lemma: **PROVED in this addendum**;
- global no-DRAW theorem: **RESTORED AS A HUMAN-PROOF CLAIM**;
- independent external re-audit: **PENDING**;
- end-to-end Lean formalization: **NOT CLAIMED**;
- JSON global-routing certificate: **still CONDITIONAL_MACHINE_CHECK for its declared typed assembly**.

The last two qualifications are important.  This addendum repairs the human
proof bridge; it does not turn the existing symbolic certificate or Lean
subset into an end-to-end formal proof.