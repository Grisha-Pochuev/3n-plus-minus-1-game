# Open proof obligations for version 5.0

**Status:** these are genuine mathematical obligations. Version 5.0 does **not** claim that they are proved, and therefore does not claim the prize problem is solved.

The purpose of this file is to prevent a future revision from hiding either obligation inside a control table, an ordinal rank, a numerical experiment, or a renamed lemma.

## P1 — Seeded A/B2 reset provenance

### Exact problem

Start with an actual DRAW carried by the typed A-selecting obligation system. A canonical A-continuation may move through temporary ordinary-source cursors

`x, A(x), A^2(x), ...`

before a B-selecting phase is reached. If the selected B transition has valuation two, the arithmetic normal form returns to an A-obligation. That return raises the finite control back to the beginning of the obligation automaton.

Before such a reset can be used in a well-founded proof, it must pay for the reset in one of two ways:

1. exhibit an **actual continuing DRAW** whose retained coefficient source is strictly below the currently ranked source; or
2. replace an already ranked finite WIN/LOSS token by a **certified strict proof-tree descendant**.

The numerical facts `B(y) < y` and “the new source is smaller than the immediate cursor” are not sufficient.

### Mandatory adversarial case

Any proposed proof of P1 must survive

`20 -> 30 -> 45 -> 68`, with `B(68)=25>20`.

Thus the source 20 retained before the streak cannot be replaced by 25 merely because the final B transition has valuation 3. The same prohibition applies a fortiori to valuation-two reset arguments that compare only with the immediate cursor.

### Acceptance criteria

A proof of P1 is acceptable only if it:

- defines exactly which finite token(s) are ranked before the first reset;
- gives the exact game-state parent/child chain proving every claimed descendant relation;
- handles A-streaks of every outcome-compatible length, not just a single A step;
- handles all four exceptional residue classes `1, 3, 12, 14 (mod 16)` without importing the ordinary side diamond;
- specifies the unique initial token installation, if one is used, and proves that it cannot be repeated at unchanged earlier rank components;
- proves that every later `b2_ready -> a_obligation` reset is strict in a previously declared rank component;
- never promotes a temporary cursor to a retained numerical anchor without a separately proved strict transition.

### What is not a proof

The following are explicitly insufficient:

- “the returned source is WIN”;
- “the returned source is smaller than the current cursor”;
- “the valuation is at least two/three”;
- a finite residue search without a theorem covering unbounded suffix lengths;
- a control-graph edge labelled as strict without a concrete descendant/source certificate.

---

## P2 — Semantic exhaustiveness of the factor/high-return router

### Exact problem

The finite control names

- `factor_fork`,
- `high_return`,
- `marked_tail`,
- `short_lift`,
- `terminal_macro`

are bookkeeping labels. To use them in a proof, every actual outcome-compatible DRAW state entering those controls must be mapped, by exact arithmetic and outcome identities, to one and only one covered row (overlap is harmless if all overlapping rows have the same certified conclusion).

Every row must then end in:

1. a pure non-reset routing step preserving the retained ranked data;
2. a genuine strict retained-source edge; or
3. a certified strict proof-token descendant edge.

Any return to a higher control without (2) or (3) is forbidden.

### Acceptance criteria

A proof of P2 is acceptable only if it contains a complete semantic transition table with, for **every** row:

- the precise arithmetic predicate/guard on the incoming game state;
- exact formulas for the two legal game children involved in the outcome split;
- the actual DRAW continuation selected by the row;
- every finite WIN/LOSS token carried through the row;
- the exact parent/child incidence that proves a token replacement is a strict descendant;
- the retained numerical source before and after the row;
- whether the row is pure routing, strict-source, or strict-token;
- coverage of every factor exponent and every returned tail length, with unbounded families handled symbolically rather than by a fixed cutoff.

A machine-readable table is useful only after these mathematical guards have been proved. A JSON graph by itself is not semantic completeness.

### High-return rows that require special attention

The review must explicitly isolate the short returned valuations (the rows where long-tail one-bit deletion no longer gives the generic formula) and prove their token provenance separately. Any generic `v >= ...` rule must state the exact threshold and prove why the omitted short rows cannot enter it.

### Terminal rows

A terminal factor macro may re-enter `a_obligation` only after the incoming marked token has been replaced by a certified lower descendant. A finite endpoint of unrelated height may be used as temporary routing data, but must **not** be inserted into the ranked token multiset solely because it is finite.

---

## Closure criterion

The unconditional no-DRAW theorem may be restored only when both P1 and P2 are proved and an adversarial audit can reconstruct every reset edge from the actual game relation without using either forbidden inference recorded in `routing_certificate_v5_0.json`.
