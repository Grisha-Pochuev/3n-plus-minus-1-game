# Global no-DRAW proof

Status: **PROVED (human proof)**. Independent external review is pending, and
the complete theorem is not yet Lean-checked. See `../AUDIT.md` for the audit
protocol and `../formal/COVERAGE.md` for the exact formalization boundary.

The final transition inventory and rank assembly also have a
[`conditional symbolic certificate`](../certificates/global-routing-certificate.md).
Its checker verifies the declared coverage and size-change graph, while four
local certificate-to-game obligations remain in the human proof. Certificate
acceptance must not be described as a full formalization.

## Theorem

For every odd positive starting integer, optimal play in the two-player
\(3n\pm1\) game reaches \(1\) after finitely many moves.

Equivalently, the conjugated game has no DRAW positions.

## Proof architecture

The local arithmetic and outcome lemmas are proved in
[`verified-results.md`](verified-results.md).  The global proof uses four
assembled statements.

1. **Proof-token order (Sections 129 and 132).**  A finite multiset \(M\)
   of canonical WIN/LOSS proof heights has ordinal rank

   \[
   \Phi(M)=\mathop{\#}_{h\in M}\omega^h.
   \]

   Replacing any token by finitely many certified lower descendants
   strictly decreases \(\Phi\).  If an ordinal projection never increases
   and its equal-projection fibres are well-founded, the whole transition
   relation is well-founded.  Equal \(\Phi\) does not by itself identify
   token states, but every token-changing edge is strict; therefore an
   equal-projection route preserves the actual token multiset.

2. **Factor attachment (Sections 130--135).**  Every marked factor scan
   retains its incoming finite proof tokens.  For a marked source
   \(b=Q_D^g(C)\) with \(D\ge3\), the marked LOSS child \(y\) and WIN child
   \(q\) have a common WIN child \(r\) with
   \(h(r)\le h(y)-1\).  Before any inner branch is followed, the scan
   replaces the carried token \(y\) by \(r\), and every exit keeps that
   lower token and its exact source attachment marked.
   The two remaining lengths \(D=1,2\) are exact lifts over the already
   marked \(q\) or \(y\).

3. **Fixed-fibre normalizer (Section 136).**  At fixed retained source and
   outer token multiset, the generic A/B obligation and factor routing is
   well-founded.  Canonical A-streaks have a proved four-side-test exit;
   valuation-two B-transfers install and then lower a finite local witness;
   higher valuations give source descent or enter factor forks that pay
   source or finite-token height; and a high return
   re-enters only the marked factor rows from item 2.  More importantly,
   every return from the generic subsystem passes through a strict
   high-return replacement before a new marked pair is installed.  The
   internal source/token rank
   \(\omega^\omega a+\Psi(N)\) therefore decreases across every such
   cross-transition.  Applying the well-founded-fibre lemma again inside
   the fixed outer fibre prevents the two subsystems from alternating
   forever.  Hence no routing path can remain forever in one fibre.

4. **Entry completeness (Section 137).**  The minimum-source
   constant-tail analysis of Sections 14--27 and the separate height-one
   analysis of Sections 69--90 have only three outputs: strict source
   descent, certified proof-token descent, or entry to the normalizer in
   item 3.  The height-one resonance is coupled across consecutive factor
   levels and is not treated by a fixed-depth search.

Assume a DRAW exists and choose the least coefficient source \(s\) of a
DRAW.  Following the exhaustive outcome diamonds gives a marked
macro-configuration containing an actual DRAW.  A macrostep either reaches
a DRAW below \(s\), strictly decreases \(\Phi\), or stays in one fixed
normalizer fibre.  The first case contradicts the choice of \(s\); the
other two are well-founded by items 1 and 3.  Thus the complete marked
transition relation is well-founded.

But every DRAW has no LOSS child and at least one DRAW child.  Repeatedly
following the DRAW continuation through the finite macro-normalizations
would create an infinite marked transition path, a contradiction.  Hence
no DRAW exists.

Every remaining state is WIN or LOSS and has finite canonical proof height.
An optimal move from WIN goes to a lower-height LOSS child, and every move
from LOSS goes to a lower-height WIN child.  The height decreases on every
move until conjugated state \(0\), which corresponds to original state
\(1\).

Odd original states divisible by three enter the conjugated state space
after one legal move, because the odd part of \(3n\pm1\) is not divisible
by three.  Therefore the conclusion holds for every odd starting value.

## Pitfall audit

The proof does not:

- propagate a minimum DRAW indefinitely along the expanding branch;
- infer DRAW from bounded `UNKNOWN` states, a large verified prefix, or an
  arbitrary-play cycle;
- use a fixed modulus to determine an unbounded alternating suffix;
- assume a fixed total A/B phase horizon;
- restart a minimum-boundary-height argument at later factor endpoints;
- replace a retained finite witness by an incomparable later witness;
- infer a lower boundary merely from a lower ordinary predecessor;
- confuse a DRAW continuation with its separate marked WIN endpoint;
- infer that the union of two terminating routing subsystems terminates
  without checking their cross-transitions.

Exact suffix lengths, forced LOSS witnesses, canonical proof heights, and
source provenance remain marked throughout the macro relation.  See
[`pitfalls.md`](pitfalls.md) for the invalid shortcuts that motivated these
requirements.
