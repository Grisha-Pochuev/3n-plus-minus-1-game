# Hostile Audit Report - Version 7.0

**Manuscript:** `3n_plus_minus_1_game_v7.0`  
**Audit date:** 11 August 2026  
**Author:** Grisha Pochuev  
**Audit type:** adversarial logical, arithmetic, provenance, compilation, and PDF-layout review

## 1. Verdict

### As an audited status manuscript: PASS

No red, orange, or yellow logical defect was found in the claims that Version 7.0 actually makes after the final theorem-by-theorem review described below. Each unconditional lemma and proposition is proved in the manuscript. The only no-DRAW theorem is explicitly conditional on a fully specified marked-router hypothesis.

### As a proof of the prize conjecture: NOT PROVED

Version 7.0 deliberately does **not** claim the all-start no-DRAW conjecture. Four global obligations remain open:

- **Z** - source-zero valuation-one bootstrap and proof that the seed cannot be consumed again in the same earlier fibre;
- **H** - legitimate installation and later continuity of the two-token long high-return pair;
- **L** - complete LOSS-anchored `D=2` raw/signed routing module;
- **E** - a disjoint, semantically exhaustive router refining every actual DRAW continuation and proving every equal-rank fibre well-founded.

The result is therefore suitable as a corrected research-status paper and as a basis for further work, but not as a request for the EUR 500 award.

This is an internal hostile audit, not independent peer review or end-to-end kernel certification.

## 2. Material reviewed

The audit compared:

1. the v1 LaTeX/PDF manuscript;
2. the v2 LaTeX/PDF manuscript;
3. the v3.0 package;
4. the v4.0 package;
5. the v5.0 audit-hardened package;
6. the v6.3 audit-hardened package;
7. the repository repair branch;
8. the detailed `docs/verified-results.md` proof ledger;
9. the previous audit correspondence and explicit counterexamples.

The version history is logically important:

- v1-v4 asserted global closure while relying on compressed supplement statements;
- v5 correctly withdrew the unconditional global theorem and isolated open provenance obligations;
- v6.3 restored an unconditional no-DRAW theorem, but a fresh audit found that two finite high-return states were promoted to ranked tokens without a provenance constructor and that the short attached routing modules were asserted complete more strongly than their proofs established;
- v7.0 keeps the valid arithmetic and local outcome diamonds but withdraws every unsupported global promotion.

## 3. Permanent negative regressions

Version 7.0 retains two explicit counterexamples that every future proof must pass.

### 3.1 Canonical coefficient is not coefficient source

With

```text
s = 1,  J(s) = 5,  a = 3 J(s) = 15,  e = 1,
p = R(3a-e) = R(44) = 22,
```

the canonical coefficient decreases from `15` to `11`, but `11 = J(3)`, so the source increases from `1` to `3`.

**Audit result:** the false implication is displayed and never used in v7.0.

### 3.2 A later B-return need not lie below a pre-streak source

```text
20 ->A 30 ->A 45 ->A 68,   B(68) = 25 > 20.
```

**Audit result:** temporary routing cursors are not treated as retained source anchors in v7.0.

## 4. Theorem-by-theorem adversarial review

### 4.1 Elementary DRAW recursion - GREEN

The proof uses only the least inductive definitions of WIN and LOSS. A DRAW has no LOSS child and cannot have all children WIN, hence has a DRAW child.

### 4.2 Alternating-suffix factorization - GREEN

The deleted alternating word is written explicitly in the two possible leading phases. Both the positive-prefix and complete-word cases are proved. Exhaustive regression: `z = 1..500000`.

### 4.3 First binary normal form - GREEN

The two original odd children are converted to `m`-coordinates exactly. The non-direct child is identified through the proved alternating-suffix factorization. Exhaustive regression: `m = 1..500000`.

### 4.4 Strict contraction of B - GREEN

The proof removes at least one binary digit and obtains

```text
B(q) <= floor(F(q)/2) <= floor((3q+1)/4) < q.
```

The case `q=1` is checked directly.

### 4.5 Constant-tail recurrence and shared boundary - GREEN

The formulas are proved uniformly for odd coefficient, both phases, and arbitrary tail exponent. The boundary identity is proved from the exact appended bit. It is not inferred from a bounded residue search.

### 4.6 Canonical source coordinates - GREEN

The final draft now gives the existence and uniqueness construction separately for even `q` and odd `q`, then factors the resulting odd coefficient uniquely as `3^k J(s)`.

### 4.7 Ordinary side relation - GREEN

The audit rejected the earlier compressed phrase “a residue check” as insufficient. The final proof:

- excludes `R(A(q))=0` explicitly;
- lists the exact nonexceptional residue table for alternating-suffix lengths one and two;
- proves both suffix cases by appending the exact one- or two-bit word;
- checks that exceptional residues do not occur consecutively.

Exhaustive regression: all ordinary states through `100000`.

### 4.8 Exceptional child-pair identity - GREEN

The four affine rows are displayed. The previously implicit endpoint `q=1`, for which the auxiliary `z` equals zero and the positive-`z` factorization lemma cannot be invoked, is now proved separately:

```text
Moves(A(1)) = Moves(2) = {1,3}
             = {Q_1^1(J(0)), Q_2^1(J(0))}.
```

This removes a genuine yellow edge case from the draft.

### 4.9 Source selector and universal source bound - GREEN

Both phase rows are proved from the parity of `A(s)` and the alternating-suffix factorization. The state-source bound follows directly from canonical coordinates.

### 4.10 Multiset proof-token rank - GREEN

The natural ordinal sum loses one coefficient at the highest replaced exponent; finitely many lower monomials cannot compensate. The manuscript sharply distinguishes:

- a finite state;
- a routing witness;
- a retained token;
- a temporary arithmetic cursor.

### 4.11 Reverse fixed-tail progress - GREEN AS A LOCAL REVERSE NORMALIZATION

For

```text
X = Q_r^e(3c), G = Q_r^e(c), H = Q_{r+1}^e(c), Y = A(G), r >= 2,
```

the exact parent and common-child identities are proved. If `X` is DRAW:

- either `H` is DRAW and one factor of three is removed;
- or `H` is WIN, necessarily `Y` is LOSS, its actual child `w` is a lower WIN, and `A(X)` is the continuing DRAW.

The manuscript explicitly says that `X -> H` is a reverse proof normalization, not a legal move. Global use is delegated to semantic router clause C2 rather than silently following a reverse edge as play.

### 4.12 Exponent-one predecessor - GREEN AS A LOCAL SPLIT

The proof no longer applies a reverse lemma whose hypothesis is `r >= 2` at `r=1`. In the ordinary row, the terminal possibility `B(P)=0` is now excluded explicitly: a wholly alternating `A(P)` places `P` in an exceptional class. This removes another yellow edge case.

The exceptional row uses the exact adjacent pair over the actual LOSS sibling.

### 4.13 Source-zero valuation table and raw selector - GREEN LOCALLY; Z OPEN GLOBALLY

The valuation table is exact by elementary 2-adic identities. The two `j=1` raw selectors are proved from binary suffixes:

- `e=0`: raw child `A(y)`;
- `e=1`: raw child `B(y)`.

The outcome split is stated only under the explicit assumption that the signed/raw pair are children of a DRAW boundary and the signed child is finite. The manuscript no longer calls the `y DRAW` branch a completed loss-sibling entry. Non-reseeding remains Obligation Z.

### 4.14 Long high-return diamond - GREEN CONDITIONALLY; H OPEN GLOBALLY

All coordinate identities and both two-level height inequalities are valid. The proof now says:

- if `u,c` are already retained, `(u,c) -> (p,b)` is strict;
- a seed may install `u,c`, but that initialization is paid by the seed component, not falsely by the token multiset.

Continuity at every later high return remains Obligation H.

### 4.15 Short marked tails D=1 and D=2 - GREEN LOCALLY; L OPEN GLOBALLY

`D=1` returns an actual child of the retained LOSS token.

For `D=2`, the first factor valuation is proved to be exactly one, and the returned source is an exact factor-free lift over the actual LOSS token, with a separate source-zero endpoint. What is not proved is that every later raw/signed exit preserves that attachment through the entire module. That is Obligation L.

### 4.16 Complete marked-router definition and conditional closure - GREEN

The manuscript defines a complete router semantically rather than by naming a JSON control graph. It requires:

1. initialization from every actual DRAW;
2. a finite outcome-compatible successor carrying an actual DRAW;
3. weak decrease of the retained well-order with legitimate source/token changes only;
4. well-foundedness of every equal-rank fibre.

The well-founded-fibre lemma is proved. Under these clauses, a DRAW would generate an infinite descending macro-path, contradicting well-foundedness. The theorem is explicitly conditional and therefore contains no hidden assumption.

## 5. Red/orange/yellow resolution table

| Earlier issue | Severity before v7 | v7 result |
|---|---:|---|
| coefficient decrease treated as source decrease | red | explicit counterexample; inference withdrawn |
| reverse factor lemma used at exponent one | red | separate complete local predecessor split |
| later B-return compared with pre-A source | red | explicit counterexample; cursors separated from anchors |
| finite high-return states silently inserted as tokens | red | height lemma retained; insertion isolated as H |
| S1 fixed-tail witness did not construct progress | red | complete local reverse-progress dichotomy |
| source-zero `j=1`, `y DRAW` called a completed entry | orange | exact local split; global bootstrap isolated as Z |
| LOSS-anchored `D=2` module compressed into prose | orange | exact first attachment proved; full module isolated as L |
| `q=1` passed to a lemma requiring positive auxiliary `z` | yellow | separate direct proof added |
| ordinary exponent-one row could mention terminal `L=0` as a child-bearing state | yellow | `L>0` explicitly proved in ordinary row |
| seed installation described as a token-rank decrease | yellow/orange | seed and multiset components separated explicitly |
| complete router inferred from declared labels | red | no unconditional exhaustiveness claim; E remains open |

## 6. Machine checks

The release regression run passed:

```text
V7.0 SUPPORTING ARITHMETIC REGRESSIONS PASSED
normal-form states checked: 1..500000
alternating-factor states checked: 1..500000
side/source-selector states checked: 1..100000
source-bound states checked: 1..100000
odd coefficients checked: up to 20000
random long-tail samples: 10000 at 512 bits
STATUS: supporting evidence only - NOT a proof of the no-DRAW conjecture
OPEN: source-zero bootstrap, high-return token continuity,
      D=2 attached module, router exhaustiveness
```

The verifier has no third-party dependencies. It checks arithmetic identities and the permanent counterexamples. It does not infer infinite WIN/LOSS classes and does not discharge Z, H, L, or E.

## 7. LaTeX and PDF audit

- LaTeX compiled with `latexmk`, `-halt-on-error`;
- three-pass references completed through `latexmk`;
- no undefined references or citations;
- no LaTeX warnings;
- no overfull or underfull boxes;
- `chktex` reported no source warning after the selected style exclusions;
- 16 A4 pages;
- all fonts embedded;
- PDF unencrypted and openable;
- all 16 pages rendered at 180 dpi and visually inspected;
- no clipping, overlap, black squares, broken glyphs, or malformed tables found;
- PDF preflight reported no structural warning.

## 8. Final trust statement

Version 7.0 is the first manuscript in this sequence whose logical safety does not depend on accepting the desired no-DRAW conclusion. Its unconditional mathematical content survived the internal hostile audit, and its remaining barrier is stated rather than hidden.

It must nevertheless be cited accurately:

> Version 7.0 gives a verified binary core, stronger local normalization lemmas, and a conditional closure theorem. It does not yet prove that every starting state has finite remoteness.
