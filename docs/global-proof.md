# Global proof status after the Althöfer audit

Status: **OPEN IN THIS MANUSCRIPT — audited repair in progress.**

The target theorem is unchanged:

> For every odd positive starting integer, optimal play in the two-player
> \(3n\pm1\) game reaches \(1\) after finitely many moves.
>
> Equivalently, the conjugated game has no `DRAW` positions.

The previous version of this file described that theorem as proved.  An
external audit by Ingo Althöfer, using an independent GPT-5.6 Sol audit,
identified a genuine gap in the entry argument of old Section 137.  The
corrected Sections 136--138 in `verified-results.md` withdraw the invalid
step and isolate the remaining obligation exactly.

## What failed in the old assembly

The old Section 137 used the implication

\[
\text{smaller canonical coefficient}
\Longrightarrow
\text{smaller coefficient source}.
\]

That implication is false when powers of three are present.  For example,
with

\[
s=1,\qquad J(1)=5,\qquad a=15,\qquad \epsilon=1,
\]

the common boundary child is

\[
R(3a-\epsilon)=R(44)=22.
\]

Its canonical coefficient is \(11<15\), but \(11=J(3)\), so its source is
\(3>1\).

The old assembly also used the reverse factor lemma of Section 16 as if it
removed factors of three from exponent one.  Section 16 starts at exponent
at least two.  Hence the family

\[
Q_1^\epsilon(3^kJ(s)),\qquad k>0,
\]

was not covered.

## What the repair now proves

Sections 79--81 give a universal two-level normalization for exactly that
missing arithmetic family.  If

\[
Q_1^\epsilon(3^kJ(s))
\]

is DRAW, then the adjacent factor scan exposes a DRAW at the current or next
factor level.  Writing

\[
3^{i+1}J(s)+1-2\epsilon=2^vJ(t),
\]

the signed exit is exactly

\[
Q_v^{1-\epsilon}(J(t)).
\]

For \(v\ge2\), its raw sibling is exactly

\[
Q_{v-1}^{1-\epsilon}(J(t)),
\]

so the exit is a factor-free lift or adjacent factor-free frame over the
returned source \(t\).  For \(v=1\), a DRAW on the positive raw side has a
genuine strict source descent relative to \(t\).

This repairs the omitted **arithmetic case split**.  It does not imply
\(t<s\), and the corrected proof never claims that it does.

## The remaining lemma

The sole global obstruction is now stated explicitly in corrected Section
137.

**Arbitrary exponent-one attachment lemma.**  Let \(s\) be the globally
least coefficient source of a DRAW and suppose

\[
Q_1^\epsilon(3^kJ(s))\text{ is DRAW},\qquad k>0.
\]

The two-level normalization must be attached to the already retained
source/proof-token data so that, after finitely many outcome-compatible
moves, one obtains one of:

1. an actual DRAW with retained source strictly below \(s\);
2. a certified strict replacement of an already carried finite proof
   token;
3. a typed entry into the Section 136 normalizer with the old retained
   source/token projection unchanged.

The returned arithmetic source \(t\) may be larger than \(s\).  It may be
used as temporary routing data, but it may not silently replace the retained
source anchor.

For \(s>0\), the ordinary state \(s\) itself is necessarily finite
(`WIN` or `LOSS`), because its own coefficient source is strictly below
\(s\).  Sections 54, 57, and 61--64 therefore provide substantial finite
proof-tree provenance for attacking the remaining attachment lemma.  The
source-zero case has its separate normalization in Sections 71--73.

## What remains valid

The external audit does not invalidate the following proved local pieces:

- the conjugated normal form and strict contraction \(B(q)<q\);
- the finite `WIN`/`LOSS` proof-height formalism;
- the exact constant-tail identities;
- the factor-level coupling of Sections 79--81;
- the multiset proof-token order of Section 129;
- the well-founded-fibre lemma of Section 132;
- the typed marked/obligation normalizer of corrected Section 136, **once a
  provenance-preserving typed entry has been established**.

The symbolic certificate remains useful only for the declared typed
assembly.  It does not certify the still-open semantic attachment of the
arbitrary factorful exponent-one family to that assembly.

## Conditional final implication

If the attachment lemma above is proved, the final contradiction argument
from the old Section 138 becomes valid again: every hypothetical DRAW gives
a finite marked macrostep; strict source or proof-token transitions cannot
occur infinitely, and an equal retained-rank path is trapped in the
well-founded typed normalizer.  Hence no infinite marked DRAW path exists.

Until that lemma is proved, however, this repository must not describe the
global theorem as established.
