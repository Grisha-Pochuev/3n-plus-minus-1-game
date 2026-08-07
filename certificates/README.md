# Machine-checkable certificates

The repository uses "certificate" in the standard proof-audit sense: a
generator may be complicated, but it emits a finite witness that a smaller,
independent checker can validate without trusting the generator.

## Implemented: finite outcome proof DAG

`scripts/extract_proof.py` generates a JSON proof that one conjugated position
is `WIN` or `LOSS`. `scripts/verify_outcome_certificate.py` is the independent
checker. It reimplements the two exact moves and verifies:

- terminal state `0` is `LOSS`;
- every certified `WIN` names an actual certified `LOSS` child;
- every certified nonterminal `LOSS` names both actual `WIN` children;
- a positive integer rank strictly decreases on every proof edge;
- every referenced node is present and every supplied node is reachable from
  the root.

Example:

```bash
python scripts/verify_outcome_certificate.py certificates/examples/q10.json
python scripts/extract_proof.py 100 --limit 200000 --output proof-100.json
python scripts/verify_outcome_certificate.py proof-100.json
```

A valid file is a genuine finite proof of its root outcome. It does not depend
on trusting the bounded retrograde generator.

## Not sufficient for the global theorem

Any collection of finite root certificates covers only the roots in that
collection. Even a very large cutoff cannot prove that no unbounded `DRAW`
kernel exists. This limitation is mathematical, not a performance issue.

For the global theorem, the useful eventual certificate is a finite symbolic
one: a complete list of marked transition schemas together with a ranking
component that strictly decreases on every cycle or routing edge. A small
checker would validate exhaustiveness of residue/valuation cases and all rank
inequalities. The proposed structure is recorded in
[`global-routing-certificate.md`](global-routing-certificate.md).

## One-command audit

An independent reader normally does not need to invoke the tools separately:

```bash
python audit.py
```

This runs the full regression suite, finite identity checks, certificate
generation, and independent certificate verification. Its final success line
must still be interpreted within the trust boundary stated in `AUDIT.md`.
