#!/usr/bin/env python3
"""Arithmetic regression for the finite high-return shadow-word lemma.

This checks identities only; it is not a proof of token provenance.
"""
from __future__ import annotations

import argparse

from optimal_3n1.game import (
    constant_tail_coordinates,
    constant_tail_state as Q,
    embedded_original_state as J,
    source_A_selecting_tail_bit as alpha,
    transformed_A as A,
    transformed_B as B,
    v2,
)


def run(x: int, word: str) -> int:
    for move in word:
        x = A(x) if move == "A" else B(x)
    return x


def levels(r: int) -> list[int]:
    todo = {(r, 0), (r + 1, 0)}
    out: set[int] = set()
    while todo:
        d, k = todo.pop()
        if d <= 2:
            out.add(k)
        else:
            todo |= {(d - 1, k + 1), (d - 2, k + 1)}
    return sorted(out)


def prefix(r: int, k: int) -> tuple[str, int]:
    if k == r - 1:
        return "A" * k, 1
    na, nb = 2 * k - r + 2, r - k - 2
    assert na >= 0 and nb >= 0 and na + nb == k
    return "A" * na + "B" * nb, 2


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--source-limit", type=int, default=100_000)
    parser.add_argument("--high-threshold", type=int, default=7)
    args = parser.parse_args()

    current = successor = path_checks = 0
    for x in range(1, args.source_limit + 1):
        e0 = alpha(x)
        g = 1 - e0
        p = Q(J(x), 1, e0)
        u = Q(J(x), 2, e0)
        retained_loss = A(p)
        opposite = A(retained_loss)
        b = B(p)
        factor_parent = A(u)
        hi = A(factor_parent)
        lo = B(factor_parent)
        ah, rh, gh = constant_tail_coordinates(hi)
        a, r, gl = constant_tail_coordinates(lo)
        assert ah == a == J(b) and rh == r + 1 and gh == gl == g
        expected_levels = list(range(max(0, (r - 1) // 2), r))
        assert levels(r) == expected_levels

        e = 1 - g
        for k in expected_levels:
            pre, d = prefix(r, k)
            c0 = (3**k) * a
            assert run(opposite, pre) == Q(c0, d, e)
            path_checks += 1

            n0 = 3 * c0 + 1 - 2 * g
            j0 = v2(n0)
            if j0 >= args.high_threshold:
                target = Q(3 * (n0 >> j0), j0 - 3, e)
                word = pre + "BA"
                assert run(opposite, word) == target
                assert run(retained_loss, "A" + word) == target
                current += 1
            elif j0 == 1:
                n1 = 9 * c0 + 1 - 2 * g
                j1 = v2(n1)
                if j1 >= args.high_threshold:
                    target = Q(3 * (n1 >> j1), j1 - 3, e)
                    word = pre + ("BAA" if d == 1 else "ABA")
                    assert run(opposite, word) == target
                    assert run(retained_loss, "A" + word) == target
                    successor += 1

    print("HIGH_RETURN_SHADOW_WORDS_OK")
    print(f"factor entries checked: {args.source_limit}")
    print(f"canonical boundary paths checked: {path_checks}")
    print(f"current-level long returns checked: {current}")
    print(f"next-level long returns checked: {successor}")
    print("scope: arithmetic identities only; no proof-token theorem inferred")


if __name__ == "__main__":
    main()
