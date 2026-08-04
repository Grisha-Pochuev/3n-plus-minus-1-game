# Instructions for Codex and other agents

## Mission

Work toward a rigorous proof that optimal play in the two-player `3n±1` game always terminates at `1`, or produce a genuine counterexample if one exists.

This is a mathematical research repository, not a benchmark for raw enumeration. The user's machine is a modest five-year-old laptop. Prefer proofs, symbolic reductions, finite automata, compact certificates, and memory-efficient experiments.

## Mandatory reading before changing anything

Read, in order:

1. `README.md`
2. `docs/problem.md`
3. `docs/normal-form.md`
4. `docs/verified-results.md`
5. `docs/proof-ledger.md`
6. `docs/pitfalls.md`
7. `docs/research-plan.md`

Run:

```bash
python -m unittest discover -s tests -v
python scripts/verify_claims.py --limit 100000
```

## Standards of proof

Every mathematical statement must be marked as one of:

- **PROVED** — accompanied by a complete proof;
- **COMPUTATIONALLY VERIFIED** — accompanied by committed code, exact parameters, and reproducible output;
- **CONJECTURE** — supported but unproved;
- **DISPROVED** — with a counterexample;
- **UNVERIFIED LEAD** — inherited from earlier discussion but not yet reproduced.

Never silently promote a computational observation to a theorem.

## Safe workflow for new ideas

1. State the proposed lemma precisely.
2. Try to falsify it on small and adversarial inputs.
3. Add a regression test for every counterexample found.
4. If it survives, seek a symbolic proof.
5. Update `docs/proof-ledger.md` and the relevant note.
6. Commit code and mathematical notes together.

## Game semantics

A state is an odd positive integer. State `1` is terminal: the player who just moved has won, so the player to move at `1` is losing.

Because infinite play is possible under arbitrary choices, the outcome space is potentially `WIN`, `LOSS`, or `DRAW`. Do not use finite-game backward induction without explicitly handling the boundary or infinite paths.

## Computational rules

- Use the standard library unless an external dependency has a clear payoff.
- Keep algorithms streaming or linear-memory where possible.
- Never treat nodes outside a finite search window as winning or losing.
- Store exact command lines and parameters with notable results.
- Prefer checkpointable computations.
- Do not launch GitHub Actions or remote brute-force runs unless the user explicitly requests them.

## High-priority mathematical directions

1. A well-founded rank compatible with `WIN/LOSS` recursion.
2. A finite-state transducer over binary suffixes plus a rank or potential.
3. A proof that no closed draw kernel can exist in the conjugated graph.
4. Structural analysis of predecessor trees and alternating binary suffixes.
5. Compact machine-checkable certificates for large finite regions, used only as lemmas toward a general proof.

## Forbidden shortcuts

Do not repeat any argument listed in `docs/pitfalls.md` without first addressing the stated flaw.

In particular:

- do not infer that an entire expanding chain is drawn from minimality of one draw;
- do not infer a global theorem from a fixed search depth;
- do not claim that a fixed modulus determines the alternating-suffix operation;
- do not claim that a strategy forcing termination necessarily forces a win.
