# Whole-problem certificate reduction — 20 August 2026

Status: **OPEN — RED**.

This note continues `proof-architecture-reset-2026-08-14.md` and
`pro-session-high-return-frontier-2026-08-14.md`. It deliberately does not
patch Section 136 in place and does not promote any historical manuscript to a
completed proof. `verified-results.md` is used only as a library of local
lemmas that survived audit.

## 1. What changed

The old proof architecture repeatedly failed at the same point: a later finite
WIN/LOSS state was treated as if its proof occurrence were automatically
inherited from an earlier ranked occurrence. Local arithmetic and local height
drops can be correct while the global rank is still invalid because the finite
certificate has been silently reseeded.

The clean restart therefore removes Section 136, the `(q,y)` pair rank, and the
one-shot entry bit from the trusted global core. The primary object is now an
actual finite WIN/LOSS certificate.

## 2. Finite certificates

For the original odd game let

```
child_-(n) = odd(3n-1)
child_+(n) = odd(3n+1).
```

`LOSS(1)` is the terminal certificate. For `n>1`, a `WIN(n)` certificate
contains one legal child with a `LOSS` certificate. A `LOSS(n)` certificate
contains `WIN` certificates for both legal children.

This distinction is essential. A WIN certificate certifies only its selected
LOSS child. It does **not** certify the other child as finite. Any proof step
that requires the unselected child needs a separate theorem.

The independent checker added in this commit validates exactly these finite
objects and also validates finite coinductive DRAW traps. It deliberately does
not infer an infinite theorem from a bounded search.

## 3. Clean whole-problem reduction

For every odd `n>1`, exactly one child is smaller and one is larger. Write

```
D(n) < n < U(n).
```

A sufficient global theorem is the following certificate-transfer principle:

> For every odd `n>1`, from any actual finite certificate of `D(n)` one can
> construct an actual finite certificate of `U(n)` by a finite, checkable set
> of certificate rules whose recursive calls are well founded.

If this transfer theorem is proved, strong induction on `n` proves that every
position is finite. Indeed, `D(n)<n`, so by induction `D(n)` has a certificate;
the transfer gives a certificate for `U(n)`; from the two child certificates
one constructs the appropriate WIN or LOSS certificate for `n`.

Conversely, if the no-DRAW theorem is already known, both children of every
position are finite. Thus at the level of existence of finite certificates the
transfer relation is necessary as well. The new research problem is stronger
and constructive: exhibit one uniform finite rule system whose termination is
itself verifiable.

This reduction is independent of the old Section 136 lifecycle.

## 4. Verified arithmetic skeleton

Put

```
epsilon(n) = +1 if n == 1 (mod 4), else -1,
b = D(n),
p = U(n),
v = v2(3n + epsilon(n)).
```

Then `v>=2` and

```
p = 2^(v-1) b - epsilon(n).
```

For `x_k = 2^k b - epsilon`, `k>=3`, the exact children are

```
U(x_k) = 2^(k-1) (3b) - epsilon,
D(x_k) = 2^(k-2) (3b) - epsilon.
```

At the boundary `k=1,2`, the two states share the child

```
y = odd(3b - epsilon).
```

These identities explain the long-tail and common-child diamonds in
`verified-results.md`. They are locally correct but do not by themselves
transport the finite certificate needed by the new global induction.

## 5. New architecture candidates and their status

### A. Structural recursion on the actual certificate

This is the leading positive route. A recursive transfer routine should either
reduce an arithmetic counter while retaining the same input certificate, or
make a recursive call on a literal strict subcertificate. Such a termination
argument can be audited directly.

Current obstruction: some boundary identities require the *other* child of a
WIN node. That child is not available from a WIN certificate. The missing
lemma must eliminate that request or derive the needed finiteness without
silently adding a certificate.

### B. Globally minimal bad configuration

This would avoid provenance bookkeeping if every locally smaller replacement
were again a semantically legal bad configuration. That closure is not proved:
a smaller numerical pair need not contain a DRAW carrier with the required
certificate polarity.

### C. State-native canonical rank

A canonical minimum over admissible witnesses would work only if every local
rule accepts that canonical minimizer and returns an admissible smaller witness
for the next state. Existing local lemmas are path-dependent and do not prove
this compatibility.

### D. Termination of every play

False. `5 -> 7 -> 5` is a legal cycle, while 5 is WIN because it also has a
move to 1. The theorem concerns finite optimal play, not arbitrary play.

### E. Bounded computation

Useful for falsification and discovery only. An unresolved boundary state is
not a DRAW certificate. A genuine negative result must be a finite
coinductive trap with WIN-certified exits.

## 6. Exact current frontier

The remaining task is now stated without Section 136:

> Build a complete finite certificate transformer from `Fin(D(n))` to
> `Fin(U(n))`. For every WIN/LOSS input polarity, every sign, and every
> long-tail/boundary case, each recursive call must either keep the same
> certificate while decreasing a natural arithmetic parameter, or receive a
> literal strict subcertificate. No branch may ask for the unselected child of
> a WIN certificate unless a separate lemma proves that child finite.

A successful solution must provide:

1. a finite list of transfer states/types;
2. exact arithmetic guards covering every odd `n>1`;
3. exact WIN/LOSS certificate input and output for every transition;
4. a finite call graph with a well-founded decrease on every cycle;
5. an independent checker that validates the finite certificate semantics;
6. a hostile audit from the original game relation to the no-DRAW conclusion.

A negative solution would instead provide a finite coinductive DRAW trap with
a trap successor at every node and a finite WIN certificate for every exit.

## 7. Independent checker

Run:

```bash
python scripts/check_game_certificates.py --self-test
```

Expected output:

```text
self-test: OK
```

The self-test checks the arithmetic sibling identity through odd `n<10001`,
accepts basic finite certificates, and rejects the tempting `5 <-> 7` cycle as
a DRAW trap because it has the LOSS exit `1`.

## 8. Research rule going forward

Do not create a new theorem-claiming manuscript until the certificate-transfer
system above is complete and has survived a fresh hostile audit. Historical
article versions and the old normalizer remain useful sources of local lemmas
and counterexamples to naive ranks, but they are not accepted global proofs.
