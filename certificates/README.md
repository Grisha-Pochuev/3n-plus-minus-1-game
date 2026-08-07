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

## Implemented: conditional global routing assembly

The repository also commits a finite symbolic inventory of the final
well-foundedness argument:

```bash
python scripts/verify_global_certificate.py
```

The checker validates total declared guard partitions, one rule per case,
lexicographic reset discipline, proof-source integrity, and acyclicity of the
equal-rank control graph. Read
[`global-routing-certificate.md`](global-routing-certificate.md) for the exact
format and trust boundary.

This is a **conditional machine check** of the global assembly. The universal
arithmetic, refinement of semantic guards to every legal game case,
outcome-compatible `DRAW` continuation, and finite productivity of each macro
remain the cited human proof obligations. The checker makes these four
obligations explicit and refuses a certificate that omits them.

## Why finite root certificates are still insufficient

Any collection of finite root certificates covers only the roots in that
collection. Even a very large cutoff cannot prove that no unbounded `DRAW`
kernel exists. This limitation is mathematical, not a performance issue. The
global assembly certificate addresses the infinite rank structure, but it is
not yet a full formal refinement from the original game relation.

## One-command audit

An independent reader normally does not need to invoke the tools separately:

```bash
python audit.py
```

This runs the full regression suite, finite identity checks, certificate
generation, and independent certificate verification. Its final success line
must still be interpreted within the trust boundary stated in `AUDIT.md`.
