#!/usr/bin/env python3
"""Finite arithmetic regression checks for 3n+-1 game article package.

These checks support the identities used in the article. They are not a proof
of the infinite theorem.
"""

from __future__ import annotations


def A(q: int) -> int:
    return (3 * q + 1) // 2


def alternating_suffix_len(n: int) -> int:
    if n == 0:
        return 0
    bits = bin(n)[2:]
    k = 1
    i = len(bits) - 1
    while i > 0 and bits[i - 1] != bits[i]:
        k += 1
        i -= 1
    return k


def R(n: int) -> int:
    return n >> alternating_suffix_len(n)


def B(q: int) -> int:
    return R(A(q))


def Q(r: int, e: int, a: int) -> int:
    return a * (1 << r) - e


def J(s: int) -> int:
    return 2 * A(s) + 1


def alpha(s: int) -> int:
    return 1 - ((s // 2) % 2)


def v2(n: int) -> int:
    assert n > 0
    return (n & -n).bit_length() - 1


def oddpart(n: int) -> int:
    return n >> v2(n)


def check_long_tail(limit_c: int, max_r: int) -> None:
    for c in range(1, limit_c + 1, 2):
        for e in (0, 1):
            for r in range(3, max_r + 1):
                assert A(Q(r, e, c)) == Q(r - 1, e, 3 * c)
                assert B(Q(r, e, c)) == Q(r - 2, e, 3 * c)
            assert B(Q(1, e, c)) == B(Q(2, e, c))


def check_fixed_tail_factor(limit_c: int, max_r: int) -> None:
    for c in range(1, limit_c + 1, 2):
        for e in (0, 1):
            for r in range(2, max_r + 1):
                X = Q(r, e, 3 * c)
                G = Q(r, e, c)
                H = Q(r + 1, e, c)
                Y = A(G)
                assert A(H) == X
                assert B(H) == Y


def check_exponent_one_lift(limit_a: int, max_k: int) -> None:
    for a in range(1, limit_a + 1, 2):
        for e in (0, 1):
            for k in range(1, max_k + 1):
                Rk = Q(1, e, (3**k) * a)
                Pprev = Q(2, e, (3 ** (k - 1)) * a)
                assert A(Pprev) == Rk


def check_base_entry(limit_x: int) -> None:
    for x in range(1, limit_x + 1):
        a = J(x)
        for e in (0, 1):
            P = Q(1, e, a)
            U = Q(2, e, a)
            b = B(P)
            assert b == B(U)
            n = 9 * a + 1 - 2 * e
            v = v2(n)
            assert oddpart(n) == J(b)
            g = 1 - e
            if e == 1 - alpha(x):
                assert v == 1, (x, e, v)
                assert b == 3 * A(x) + 1, (x, e, b, A(x))
                # Raw child is an ordinary child of b.
                T = Q(1, g, J(b))
                C = R(T)
                assert C in (A(b), B(b)), (x, e, b, C, A(b), B(b))
            else:
                assert e == alpha(x)
                assert v >= 2, (x, e, v)
                if v >= 4:
                    assert b < x, (x, e, v, b)
                if v == 3:
                    assert J(b) % 3 == (1 + g) % 3, (x, e, b, g)


def main() -> None:
    check_long_tail(limit_c=20001, max_r=16)
    check_fixed_tail_factor(limit_c=20001, max_r=16)
    check_exponent_one_lift(limit_a=5001, max_k=9)
    check_base_entry(limit_x=200000)
    print("v3.0 arithmetic regression checks passed")


if __name__ == "__main__":
    main()
