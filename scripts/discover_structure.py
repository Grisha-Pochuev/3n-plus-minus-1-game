#!/usr/bin/env python3
"""Search for finite-state structure in a boundary-safe solved prefix.

This is a discovery tool, not a proof.  It builds one retrograde table and
reuses it for several diagnostics so that exploratory runs remain suitable
for a modest laptop.
"""

from __future__ import annotations

import argparse
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from optimal_3n1.game import inverse_F, transformed_A, transformed_B  # noqa: E402
from optimal_3n1.retrograde import Outcome, bounded_retrograde  # noqa: E402


def a_coordinates(q: int) -> tuple[int, int]:
    """Return (A-root, depth) in the unique expanding A-ray containing q."""
    depth = 0
    while q > 0 and q % 3 != 1:
        predecessor = inverse_F(q)
        if predecessor is None:
            raise AssertionError(q)
        q = predecessor
        depth += 1
    return q, depth


def approximate_kernel_counts(labels: bytes, base: int, sample: int) -> list[tuple[int, int, int]]:
    """Count sampled members of the base-kernel of a finite label sequence."""
    result = []
    stride = 1
    while stride < len(labels):
        length = min(sample, (len(labels) - 1) // stride + 1)
        signatures = {
            bytes(labels[offset + stride * index] for index in range(length) if offset + stride * index < len(labels))
            for offset in range(stride)
        }
        result.append((stride, len(signatures), length))
        stride *= base
    return result


def shortest_move_word(start: int, target: int, max_depth: int) -> str | None:
    """Find a shortest A/B word mapping start to target, for diagnostics."""
    frontier = {start: ""}
    seen = {start}
    for _ in range(max_depth + 1):
        if target in frontier:
            return frontier[target]
        following: dict[int, str] = {}
        for value, word in frontier.items():
            for letter, child in (("A", transformed_A(value)), ("B", transformed_B(value))):
                if child not in seen:
                    seen.add(child)
                    following[child] = word + letter
        frontier = following
    return None


def side_win_assumption_contradiction(start: int, length: int) -> bool:
    """Propagate exact W/L implications for a proposed all-W side run.

    This uses only the game recursion.  It deliberately does not consult a
    retrograde table, so a returned contradiction is a symbolic one.
    """
    wins: set[int] = set()
    losses: set[int] = set()
    q = start
    for _ in range(length):
        wins.add(transformed_B(q))
        q = transformed_A(q)

    changed = True
    while changed:
        if wins & losses:
            return True
        changed = False

        for value in tuple(losses):
            for child in (transformed_A(value), transformed_B(value)):
                if child not in wins:
                    wins.add(child)
                    changed = True

        for value in tuple(wins):
            child_a = transformed_A(value)
            child_b = transformed_B(value)
            if child_a in losses or child_b in losses:
                continue
            if child_a in wins and child_b in wins:
                return True
            if child_a in wins and child_b not in losses:
                losses.add(child_b)
                changed = True
            elif child_b in wins and child_a not in losses:
                losses.add(child_a)
                changed = True

    return bool(wins & losses)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=3_000_000)
    parser.add_argument("--prefix", type=int, default=65_536)
    parser.add_argument("--sample", type=int, default=128)
    args = parser.parse_args()

    result = bounded_retrograde(args.limit)
    prefix = min(args.prefix, result.resolved_prefix_end() + 1)
    if prefix < args.prefix:
        raise SystemExit(
            f"requested prefix {args.prefix:,} is not solved at limit {args.limit:,}; "
            f"safe prefix is {prefix:,}"
        )

    labels = bytes(1 if result.outcome(q) == Outcome.LOSS else 2 for q in range(prefix))
    print(f"retrograde limit: {args.limit:,}")
    print(f"boundary-safe prefix analyzed: 0 <= q < {prefix:,}")

    for base in (2, 3, 4, 6):
        print(f"approximate {base}-kernel (stride, signatures, sampled terms):")
        for row in approximate_kernel_counts(labels, base, args.sample):
            print(" ", row)

    for modulus in (4, 8, 16, 32, 64):
        classes: dict[tuple[int, int], set[int]] = defaultdict(set)
        for q in range(1, prefix):
            root, depth = a_coordinates(q)
            classes[(root % modulus, depth % modulus)].add(labels[q])
        pure = sum(len(values) == 1 for values in classes.values())
        print(
            f"A-coordinate residues mod {modulus}: "
            f"{pure:,}/{len(classes):,} classes have one observed outcome"
        )

    for scale in range(2, 13):
        deterministic = []
        for offset in range(scale):
            pairs = set()
            for q in range(1, (prefix - 1 - offset) // scale + 1):
                pairs.add((labels[q], labels[scale * q + offset]))
                if len(pairs) == 4:
                    break
            if len(pairs) <= 2:
                deterministic.append((offset, sorted(pairs)))
        if deterministic:
            print(f"scale {scale}: low-complexity affine observations {deterministic}")

    relation_counts: dict[str, int] = defaultdict(int)
    relation_outcomes: dict[str, dict[tuple[str, str], int]] = defaultdict(lambda: defaultdict(int))
    relation_example: dict[str, tuple[int, int, int]] = {}
    for q in range(1, prefix):
        side = transformed_B(q)
        next_side = transformed_B(transformed_A(q))
        word = shortest_move_word(side, next_side, max_depth=6)
        key = word if word is not None else "UNMATCHED"
        relation_counts[key] += 1
        relation_example.setdefault(key, (q, side, next_side))
        if next_side <= result.limit:
            pair = (result.outcome(side).name, result.outcome(next_side).name)
            relation_outcomes[key][pair] += 1
    print("shortest words taking B(q) to B(A(q)):")
    for word, count in sorted(relation_counts.items(), key=lambda item: (-item[1], item[0])):
        print(
            f"  {word or 'identity'}: {count:,}; example={relation_example[word]}; "
            f"outcome pairs={dict(relation_outcomes[word])}"
        )

    longest = (0, 0, 0)
    for root in range(1, prefix, 3):
        q = root
        run = 0
        run_start = q
        while q < prefix:
            if result.outcome(q) == Outcome.WIN:
                if run == 0:
                    run_start = q
                run += 1
                longest = max(longest, (run, root, run_start))
            else:
                run = 0
            q = transformed_A(q)
    print(f"longest observed WIN run on one A-ray: {longest}")

    longest_consistent = (0, 0)
    search_starts = min(prefix, 100_000)
    for start in range(1, search_starts):
        length = 1
        while length <= 64 and not side_win_assumption_contradiction(start, length):
            length += 1
        longest_consistent = max(longest_consistent, (length - 1, start))
    print(
        "longest side-W prefix not refuted by local W/L propagation "
        f"for starts below {search_starts:,}: {longest_consistent}"
    )
    print("Interpretation: every line above is computational evidence only.")


if __name__ == "__main__":
    main()
