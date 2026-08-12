#!/usr/bin/env python3
"""Supporting arithmetic regressions for Version 7.0.

This program checks finite instances of identities proved in the paper and
permanent counterexamples to withdrawn shortcuts.  It does NOT prove the
no-DRAW conjecture and does not check the four open global obligations.
"""
from __future__ import annotations

import argparse
import random
from typing import Tuple

EXCEPTIONAL = {1, 3, 12, 14}


def A(q: int) -> int:
    if q < 0:
        raise ValueError(q)
    return (3 * q + 1) // 2


def asl(n: int) -> int:
    if n < 0:
        raise ValueError(n)
    if n == 0:
        return 0
    k = 1
    bit = n & 1
    n >>= 1
    while n:
        nxt = n & 1
        if nxt == bit:
            break
        k += 1
        bit = nxt
        n >>= 1
    return k


def R(n: int) -> int:
    return n >> asl(n)


def B(q: int) -> int:
    return R(A(q))


def J(s: int) -> int:
    return 2 * A(s) + 1


def Q(r: int, e: int, a: int) -> int:
    assert r >= 0 and e in (0, 1) and a > 0 and a % 2 == 1
    return a * (1 << r) - e


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def oddpart(n: int) -> int:
    return n >> v2(n)


def constant_tail(q: int) -> Tuple[int, int, int]:
    assert q > 0
    if q % 2 == 0:
        return oddpart(q), v2(q), 0
    return oddpart(q + 1), v2(q + 1), 1


def source_of_three_free(a: int) -> int:
    assert a > 0 and a % 2 == 1 and a % 3 != 0
    s0 = max(0, (a - 2) // 3)
    for s in range(max(0, s0 - 2), s0 + 4):
        if J(s) == a:
            return s
    raise AssertionError((a, s0))


def coeff_source(a: int) -> Tuple[int, int]:
    assert a > 0 and a % 2 == 1
    k = 0
    while a % 3 == 0:
        a //= 3
        k += 1
    return source_of_three_free(a), k


def rho(q: int) -> int:
    a, _, _ = constant_tail(q)
    return coeff_source(a)[0]


def odd_original_children(n: int) -> Tuple[int, int]:
    assert n > 1 and n % 2 == 1
    x = oddpart(3 * n - 1)
    y = oddpart(3 * n + 1)
    return tuple(sorted((x, y)))


def m_children(m: int) -> Tuple[int, int]:
    n = 2 * m + 1
    return tuple(sorted(((x - 1) // 2 for x in odd_original_children(n))))


def factor_free_pair_over(children: Tuple[int, int], source: int) -> bool:
    data = []
    for q in children:
        a, r, e = constant_tail(q)
        s, k = coeff_source(a)
        data.append((s, k, r, e))
    (s1, k1, r1, e1), (s2, k2, r2, e2) = data
    return s1 == s2 == source and k1 == k2 == 0 and e1 == e2 and abs(r1 - r2) == 1


def check_normal_form(limit: int) -> None:
    for m in range(1, limit + 1):
        got = m_children(m)
        want = tuple(sorted((A(m), A(R(m)))))
        assert got == want, (m, got, want)
        assert B(m) < m


def check_alternating_factorization(limit: int) -> None:
    for z in range(1, limit + 1):
        delta = 1 - (z & 1)
        N = 3 * z + 1 + delta
        k = v2(N)
        assert oddpart(N) == J(R(z)), (z, delta, N, k, R(z))
        expected = asl(z) if R(z) > 0 else z.bit_length() + 1
        assert k == expected, (z, k, expected, R(z))


def check_side_and_source_identities(limit: int) -> None:
    for q in range(1, limit + 1):
        if q % 16 not in EXCEPTIONAL:
            assert B(A(q)) in (A(B(q)), B(B(q))), q
        else:
            assert A(q) % 16 not in EXCEPTIONAL, q
            assert factor_free_pair_over((A(A(q)), B(A(q))), B(q)), q

    for s in range(1, limit + 1):
        alpha = 1 - ((s // 2) & 1)
        for e in (0, 1):
            N = 3 * J(s) + 1 - 2 * e
            vv = v2(N)
            t = source_of_three_free(oddpart(N))
            if e == alpha:
                assert vv == 1 and t == A(s), (s, e, vv, t)
            else:
                assert vv >= 2 and t == B(s), (s, e, vv, t)


def check_long_tail(limit_a: int, max_r: int) -> None:
    for a in range(1, limit_a + 1, 2):
        for e in (0, 1):
            assert B(Q(1, e, a)) == B(Q(2, e, a))
            for r in range(3, max_r + 1):
                assert A(Q(r, e, a)) == Q(r - 1, e, 3 * a)
                assert B(Q(r, e, a)) == Q(r - 2, e, 3 * a)


def check_sources(limit: int) -> None:
    for s in range(limit + 1):
        assert J(s) % 2 == 1 and J(s) % 3 != 0
        assert source_of_three_free(J(s)) == s
    for q in range(1, limit + 1):
        assert rho(q) <= (q - 1) // 6


def check_permanent_counterexamples() -> None:
    assert J(1) == 5
    p = R(3 * (3 * J(1)) - 1)
    assert p == 22
    a, _, _ = constant_tail(p)
    assert a == 11 and J(3) == 11
    assert [20, A(20), A(A(20)), A(A(A(20)))] == [20, 30, 45, 68]
    assert B(68) == 25 and B(68) > 20


def check_fixed_tail_progress(limit_c: int, max_r: int) -> None:
    for c in range(1, limit_c + 1, 2):
        for e in (0, 1):
            for r in range(2, max_r + 1):
                X = Q(r, e, 3 * c)
                G = Q(r, e, c)
                H = Q(r + 1, e, c)
                Y = A(G)
                assert {A(H), B(H)} == {X, Y}
                w = B(X)
                if r == 2:
                    assert w == B(Y)
                else:
                    assert w == A(Y)


def check_exponent_one_progress(limit_a: int, max_k: int) -> None:
    for a in range(1, limit_a + 1, 2):
        for e in (0, 1):
            power = 1
            for k in range(1, max_k + 1):
                power *= 3
                X = Q(1, e, power * a)
                P = Q(2, e, (power // 3) * a)
                assert A(P) == X
                L = B(P)
                if P % 16 not in EXCEPTIONAL:
                    assert L > 0, (a, e, k, P, X, L)
                    assert B(X) in (A(L), B(L)), (a, e, k, P, X, L)
                else:
                    assert factor_free_pair_over((A(X), B(X)), L), (a, e, k, P, X, L)


def zero_expected_j(n: int, e: int) -> int:
    if e == 0:
        return 2 if n % 2 == 1 else 1
    return 1 if n % 2 == 1 else 2 + v2(n)


def check_zero_source(max_n: int) -> None:
    for n in range(1, max_n + 1):
        p3 = 3 ** n
        for e in (0, 1):
            N = p3 + 1 - 2 * e
            j = v2(N)
            assert j == zero_expected_j(n, e), (n, e, j)
            y = source_of_three_free(oddpart(N))
            if j == 1:
                assert y == (3 ** (n - 1) - 1) // 2
                T = Q(1, 1 - e, J(y))
                raw = R(T)
                want = A(y) if e == 0 else B(y)
                assert raw == want, (n, e, y, T, raw, want)


def check_high_return(limit_t: int, max_v: int) -> None:
    for t in range(1, limit_t + 1):
        for g in (0, 1):
            for vv in range(7, max_v + 1):
                u = Q(vv - 1, g, J(t))
                c = Q(vv - 3, g, 3 * J(t))
                assert B(u) == c
                p = B(A(u))
                assert p == A(c) == Q(vv - 4, g, 9 * J(t))
                b = B(p)
                assert b == Q(vv - 6, g, 27 * J(t))


def check_short_tails(limit_c: int) -> None:
    for C in range(1, limit_c + 1, 2):
        for g in (0, 1):
            # D = 1
            b = Q(1, g, C)
            y = A(b)
            N = 9 * J(b) + 1 - 2 * g
            j = v2(N)
            w = source_of_three_free(oddpart(N))
            assert j >= 2
            assert w == (A(y) if j == 2 else B(y))

            # D = 2
            b = Q(2, g, C)
            y = B(b)
            N = 9 * J(b) + 1 - 2 * g
            assert v2(N) == 1
            w = source_of_three_free(oddpart(N))
            if y == 0:
                assert rho(w) == 0
            else:
                a, m, d = constant_tail(w)
                s, k = coeff_source(a)
                assert s == y and k == 0 and d == 1 - g and m >= 2, (C, g, y, w, (a, m, d, s, k))


def random_large_checks(samples: int, bits: int, seed: int) -> None:
    rng = random.Random(seed)
    for _ in range(samples):
        a = rng.getrandbits(bits) | 1
        e = rng.randrange(2)
        r = rng.randrange(3, 50)
        assert A(Q(r, e, a)) == Q(r - 1, e, 3 * a)
        assert B(Q(r, e, a)) == Q(r - 2, e, 3 * a)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=100_000)
    parser.add_argument("--source-limit", type=int, default=50_000)
    parser.add_argument("--coeff-limit", type=int, default=10_000)
    parser.add_argument("--max-r", type=int, default=18)
    parser.add_argument("--max-k", type=int, default=8)
    parser.add_argument("--max-v", type=int, default=18)
    parser.add_argument("--zero-n", type=int, default=100)
    parser.add_argument("--random-samples", type=int, default=2_000)
    parser.add_argument("--random-bits", type=int, default=256)
    parser.add_argument("--seed", type=int, default=70311)
    args = parser.parse_args()

    check_normal_form(args.limit)
    check_alternating_factorization(args.limit)
    check_long_tail(args.coeff_limit, args.max_r)
    check_sources(args.source_limit)
    check_side_and_source_identities(args.source_limit)
    check_permanent_counterexamples()
    check_fixed_tail_progress(args.coeff_limit, args.max_r)
    check_exponent_one_progress(min(args.coeff_limit, 2_000), args.max_k)
    check_zero_source(args.zero_n)
    check_high_return(min(args.coeff_limit, 5_000), args.max_v)
    check_short_tails(min(args.coeff_limit, 20_000))
    random_large_checks(args.random_samples, args.random_bits, args.seed)

    print("V7.0 SUPPORTING ARITHMETIC REGRESSIONS PASSED")
    print(f"normal-form states checked: 1..{args.limit}")
    print(f"alternating-factor states checked: 1..{args.limit}")
    print(f"side/source-selector states checked: 1..{args.source_limit}")
    print(f"source-bound states checked: 1..{args.source_limit}")
    print(f"odd coefficients checked: up to {args.coeff_limit}")
    print(f"random long-tail samples: {args.random_samples} at {args.random_bits} bits")
    print("STATUS: supporting evidence only - NOT a proof of the no-DRAW conjecture")
    print("OPEN: source-zero bootstrap, high-return token continuity, D=2 attached module, router exhaustiveness")


if __name__ == "__main__":
    main()
