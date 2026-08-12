# Audit report for `3n_plus_minus_1_game_v6.3`

Date: 11 August 2026

## Status of this package

This package is the audit-hardened synthesis of the earlier article/proof generations. It was produced by rebuilding the global bridge rather than restoring the previously rejected shortcuts.

**Current internal hostile-audit result:** no red or orange mathematical/logical defect was found in the final v6.3 manuscript after the repair-and-recheck cycle described below.

This sentence reports the result of the present audit; it is not a claim of independent peer acceptance or end-to-end formal verification.

## Permanently withdrawn arguments

The manuscript never uses either of the following invalid implications.

1. A smaller canonical odd coefficient does **not** imply a smaller coefficient source in the presence of powers of three. The retained regression is
   `s=1, J(1)=5, a=15, e=1`, for which the common child is `22`, its coefficient is `11<15`, but `11=J(3)`, so the source grows `1 -> 3`.
2. A later `B` return after several canonical `A` steps is not compared with the numerical cursor that preceded the streak. The retained regression is
   `20 -> 30 -> 45 -> 68`, with `B(68)=25>20`.

The reverse-factor lemma is used only at tail exponent at least two, never at exponent one.

## Red/orange repairs incorporated in v6.3

- separated retained rank anchors from temporary routing cursors;
- restored two one-shot seed layers with the order `eta` before `zeta`, and prohibited same-fibre reseeding;
- replaced the former P1 pre-streak numerical comparison by exact raw/second-selector identities;
- removed the P1 <-> P2 circular dependency: P1 stops once a route is attached to a retained token;
- removed the short-lift <-> terminal circular dependency: arithmetic transport is proved before terminal payment;
- split the long high-return canonical and factor branches; only the factor branch installs a marked tail;
- corrected the short marked-tail orientation:
  - `D=1`: `q=B(b)` WIN, `y=A(b)` LOSS;
  - `D=2`: `q=A(b)` WIN, `y=B(b)` LOSS;
  - `D>=3`: stable orientation `q=A(b)` WIN, `y=B(b)` LOSS;
- proved that the apparent `D=1, j=1` lift row is arithmetically empty;
- separated `D=2` from the `D=3` terminal module and retained its exact LOSS provenance;
- made the `D=3` strict payment `y -> r` occur before any raw/signed factor exit;
- included the zero-recycle `m=2` terminal barrier explicitly;
- corrected the logical order in that `m=2` proof: the common WIN child is proved from the LOSS parent before the continuing parent is concluded DRAW;
- kept the exponent-one terminal branch distinct from the exponent-two/three barriers;
- made every ranked token insertion/replacement refer to an actual finite state with proved parent/child provenance.

## Structural audit

Run:

```bash
python verify_structure_v6_3.py
```

Final result:

```text
V6.3 STRUCTURAL RED/ORANGE AUDIT CHECKS PASSED
former v5 controls covered: 15
labeled theorem/lemma nodes checked for direct cycles: 48
direct reference cycles: none
```

The script checks, among other things:

- coverage of all 15 high-risk v5 control classes;
- absence of a direct P1/P2 citation cycle;
- absence of a short-lift/terminal citation cycle;
- explicit `D=1`, `D=2`, `D>=3` marked-tail guards;
- high-return branch separation;
- seed ordering and non-reseeding text;
- the permanent negative regressions.

This is structural bookkeeping support, not a proof by computation.

## Arithmetic regressions

Final large run:

```bash
python verify_v6_3.py --limit 500000 --random-samples 10000 --random-bits 512
```

Result:

```text
V6.3 SUPPORTING REGRESSIONS PASSED
finite sources checked: 1..500000
second-selector counts: {'ordinary': 375000, 'B2': 250000, 'exceptional_B': 125000}
random selector samples: 10000 at 512 bits
```

The checks include the selector identities, base-entry formulas, high-return orientation table, `D=1` strict valuation, `D=2` exact lift, marked-tail common children, attached exponent-one descent, terminal `m=2` identities, and both permanent counterexamples.

## LaTeX/PDF checks

- 3 consecutive `pdflatex -halt-on-error` passes: success;
- unresolved references: none;
- overfull boxes: none reported in the final pass;
- PDF preflight: 34 A4 pages, openable, unencrypted, not scanned;
- all 34 pages rendered at 150 dpi and inspected as a contact sheet;
- key pages (title/abstract, P1, terminal proof, semantic inventory, references) inspected separately;
- no clipped text, overlaps, black squares, or broken glyphs observed.

## Verification boundary

The article is a human mathematical proof. The Python files are supporting regression and bookkeeping checks. The package does **not** claim an end-to-end Lean proof or independent peer acceptance. A new independent hostile audit remains valuable precisely because the earlier versions demonstrated that a long proof can hide a global attachment error even when its local arithmetic is extensively tested.
