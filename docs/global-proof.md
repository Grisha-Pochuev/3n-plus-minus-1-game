# Global no-DRAW proof after the Althöfer audit

Status: **HUMAN-PROOF CLAIM RESTORED; INDEPENDENT RE-AUDIT PENDING.**

The target theorem is:

> For every odd positive starting integer, optimal play in the two-player
> \(3n\pm1\) game reaches \(1\) after finitely many moves.
>
> Equivalently, the conjugated game has no `DRAW` positions.

The old Section 137 contained a real gap.  The conservative repair in
`verified-results.md` withdrew the invalid step and left the theorem open.
The missing attachment is now supplied in
[`althoefer-audit-closure.md`](althoefer-audit-closure.md).  The addendum is
the authoritative continuation after corrected Sections 136--138.

## 1. What remains withdrawn

The proof does **not** use either of the statements rejected by the audit.

1. A smaller canonical coefficient is not treated as a smaller coefficient
   source when powers of three are present.  The counterexample
   `s=1, J(1)=5, a=15, e=1` remains valid.
2. The reverse-factor lemma of Section 16 is used only from exponent at least
   two; exponent-one powers of three are handled by Sections 79--81 and the
   predecessor reduction.

## 2. Order-theoretic backbone

Section 129 assigns every finite multiset `M` of certified WIN/LOSS proof
heights the well-founded ordinal multiset rank `Phi(M)`.  Replacing any
existing token by finitely many certified lower descendants strictly lowers
that rank.

Section 132 supplies the well-founded-fibre principle.  A strict source edge
may reset later data; at fixed source a strict proof-token replacement may
reset all still-later routing data.  Equal retained source/token fibres must
be well-founded on their own.

Corrected Section 136 proves that the typed obligation/factor relation of
Sections 91--135 is well-founded in such a fixed retained fibre.  Temporary
ordinary sources such as `x,A(x),A^2(x)` are routing cursors.  They are not
silently substituted for the retained source anchor.

## 3. The missing one-shot entry component

The Althöfer gap was precisely the transition from an arbitrary raw entry to
that typed normalizer.  The closure addendum inserts one finite component

\[
\eta\in\{1,0\},\qquad 1>0,
\]

after the retained outer source and outer proof-token multiset.

- `eta=1`: the current outer fibre has not initialized its typed inner
  normalizer.
- `eta=0`: the typed Section 136 normalizer is active.

The transition

\[
\eta:1\to0
\]

is strict.  Therefore the first inner arithmetic source may be any finite
value, even a returned source `t>s`.  The proof never calls this a source
descent.  Once `eta=0`, it cannot reset to `1` in the same outer source/token
fibre.  A later raw reset is permitted only after an earlier outer source or
proof-token component has genuinely decreased.

This separates a one-time initialization from a forbidden height/source
reset and is the central order-theoretic repair.

## 4. Arbitrary factorful exponent one

Suppose

\[
Q_1^e(3^kJ(s))\text{ is DRAW},\qquad k>0.
\]

Sections 79--81 give a universal current/next-factor exit.  The corrected
Section 137 predecessor reduction sharpens it:

- either a factor-free DRAW is recovered over the original source `s`;
- or an exact factor-free DRAW lift/frame is exposed while an actual finite
  predecessor token is replaced by a certified lower descendant.

Thus an arbitrary power of three at exponent one cannot produce an unmarked
restart.  The second alternative is already a strict Section 129 edge and
may reset the inner routing task.  The first alternative reduces to the
factor-free base entry below.

## 5. Factor-free exponent-two base entry

Let

\[
a=J(x),\quad P=Q_1^e(a),\quad U=Q_2^e(a),
\]

\[
b=B(P)=B(U),\quad F=A(U)=Q_1^e(3a),\quad g=1-e.
\]

At the globally minimum DRAW source, `U DRAW` makes the common child `b`
WIN and therefore forces `F` DRAW.  Corrected Section 137 proves

\[
\boxed{9J(x)+1-2e=2^vJ(b).}
\]

The closure addendum splits by the source phase.

### B-selecting phase

If `e=1-alpha(x)`, then

\[
\boxed{v=1},\qquad \boxed{b=3A(x)+1}.
\]

The DRAW state `F` has children

\[
T=Q_1^g(J(b)),\qquad C=R(T),
\]

and Section 119 identifies `C` as an actual ordinary child of `b`.

- `T DRAW` is the first alternative of the exact obligation `O(b,g)` and
  consumes the one-shot entry bit.
- `C DRAW` makes the other ordinary child of the WIN state `b` an actual LOSS
  token.  The ordinary side diamond gives a lower boundary token; the
  exceptional A-child row is Section 68's exact frame over that LOSS token;
  and the remaining exceptional B-child row has strict coefficient source
  `<x` by the explicit estimate in the closure addendum.

Hence no B-selecting base row is untyped.

### A-selecting phase

If `e=alpha(x)`, then `v>=2`.

For `v>=4`, the exact factorization gives

\[
16J(b)\le9J(x)+1\le27x+19,
\]

hence

\[
\boxed{b\le(9x+1)/16<x}.
\]

Thus a DRAW child of `F` is a strict source exit.

At `v=2`, `F` is exactly a DRAW parent of the exponent-two/one pair over
`b`, so `O(b,g)` holds.

At `v=3`, the frame is

\[
Q_3^g(J(b)),\qquad Q_2^g(J(b)).
\]

Reducing the constructor equation modulo three gives

\[
\boxed{J(b)\equiv1+g\pmod3},
\]

which is exactly the additional hypothesis required by Section 89.  Hence
Sections 87--90 legitimately normalize this frame to a strict source/token
edge or a typed obligation.  Section 89 is not applied to an arbitrary first
frame.

This closes the factor-free exponent-two base case that remained open in the
9 August repair note.

## 6. Complete marked relation

Use the lexicographic retained data

\[
(\text{outer source},\ \Phi(M),\ \eta,\ \text{typed inner rank}).
\]

Every outcome-compatible macrostep now has one of the following forms.

1. **Outer source decrease.**  The first component strictly falls and all
   later data may reset.
2. **Finite proof-token decrease.**  The source is fixed and Section 129
   strictly lowers `Phi(M)`; later entry/inner data may reset.
3. **Initial typed entry.**  The first two components are fixed and
   `eta:1->0`; the new inner source may be numerically larger.
4. **Typed routing.**  `eta=0` and the path stays in the well-founded
   Section 136 fibre until a preceding strict component falls.

There is no fifth unranked transition after the closure addendum.

Section 132 therefore makes the complete marked macro-relation
well-founded.

## 7. Excluding DRAW

Assume a DRAW exists and choose the least coefficient source `s` occurring
at a DRAW.  Sections 14--17, 69--90, the corrected Section 137 predecessor
reduction, and the closure addendum supply a finite marked macrostep
containing an actual DRAW.

A DRAW has no LOSS child and at least one DRAW child, so unless a strict
smaller-source contradiction has already occurred the construction can be
repeated.  An infinite DRAW would therefore create an infinite path in the
marked macro-relation.

That is impossible by Section 6.  Hence

\[
\boxed{\text{there are no DRAW positions in the conjugated game}.}
\]

Every position is consequently WIN or LOSS with finite canonical proof
height.  Optimal play decreases the appropriate finite outcome height until
conjugated state `0`, which is original odd state `1`.  Odd original states
divisible by three enter the conjugated image after one legal move, so the
conclusion holds for every odd positive start.

## 8. Verification boundary

This is again a **human proof claim**.  It is not an assertion that the whole
theorem is formally verified.

- `tests/test_althoefer_closure.py` regression-checks the new phase/valuation,
  raw-child, strict-source, and Section 89 congruence identities on a finite
  range.
- `certificates/global-routing.json` remains a conditional machine check of
  the declared typed assembly; it does not itself prove the one-shot bridge.
- Lean checks only the subset listed in `formal/COVERAGE.md`.
- Independent external re-audit of this repaired entry bridge remains
  pending.
