# Proposed global routing certificate

Status: **DESIGN DOCUMENT; NOT YET AN IMPLEMENTED CERTIFICATE**.

Finite outcome DAGs cannot prove the infinite no-`DRAW` theorem. A useful
global certificate should instead encode the finite symbolic transition
inventory behind Sections 129–138 of `docs/verified-results.md`.

## Proposed record for each transition schema

```text
schema identifier
source control state
guard:
  parity/residue conditions
  valuation interval or exact value
  tail-length constraints
target control state
rank effect:
  source delta
  retained-token replacement
  fixed-fibre inner-rank delta
human-proof reference
```

## Checker obligations

An independent checker should verify four separate properties.

1. **Arithmetic validity.** Under the guard, the stated `A`/`B`, constant-tail,
   source, and valuation formulas are identities.
2. **Coverage.** Guards leaving every control state are mutually exhaustive
   for all legal parameters. Overlap is allowed only when target claims agree.
3. **Outcome compatibility.** Every macro edge retains the actual `DRAW` being
   followed and the exact finite `WIN`/`LOSS` witnesses it uses.
4. **Size change.** Each edge lowers the outer source/token projection or lies
   inside a fixed projection fibre; every cycle in a fibre has a strict inner
   rank edge.

## Why this is preferable to raw enumeration

The certificate would be finite because it stores transition schemas, not
integer positions. Unbounded suffix length and valuations remain symbolic
parameters. The checker can therefore establish a universal statement if the
coverage and arithmetic obligations are complete.

## Implementation rule

Until this format has a generator, checker, committed example, and passing
tests, it must not be described as a machine-checked proof. The current global
theorem remains a human proof, and `formal/COVERAGE.md` remains authoritative
for Lean coverage.
