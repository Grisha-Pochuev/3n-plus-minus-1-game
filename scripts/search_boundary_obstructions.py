#!/usr/bin/env python3
"""Search local outcome constraints around a hypothetical DRAW/WIN boundary.

This is a discovery tool, not a proof.  It fixes a DRAW node with exactly one
WIN child, designates a minimum-height LOSS witness of that WIN child, and
asks whether a bounded forward neighbourhood is consistent with the exact
WIN/LOSS/DRAW recursion while forbidding a DRAW parent of the resulting
strictly lower-height WIN nodes.
"""

from __future__ import annotations

import argparse
import sys
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from optimal_3n1.game import (  # noqa: E402
    constant_tail_coordinates,
    constant_tail_source_coordinates,
    constant_tail_state,
    embedded_original_state,
    inverse_F,
    source_boundary_transition,
    source_A_selecting_tail_bit,
    transformed_A,
    transformed_B,
    transformed_moves,
    v2,
)

D, W, L = 0, 1, 2
ALL = frozenset((D, W, L))


def allowed(parent: int, first: int, second: int) -> bool:
    if parent == L:
        return first == W and second == W
    if parent == W:
        return first == L or second == L
    return first != L and second != L and (first == D or second == D)


def neighbourhood(start: int, depth: int) -> tuple[set[int], list[tuple[int, int, int]]]:
    nodes = {start}
    constraints: list[tuple[int, int, int]] = []
    frontier = {start}
    for _ in range(depth):
        following: set[int] = set()
        for parent in frontier:
            if parent == 0:
                continue
            first, second = transformed_moves(parent)
            constraints.append((parent, first, second))
            following.update((first, second))
        nodes.update(following)
        frontier = following
    return nodes, constraints


def multi_neighbourhood(
    starts: set[int], depth: int
) -> tuple[set[int], list[tuple[int, int, int]]]:
    """Return the deduplicated forward neighbourhood of several roots."""
    nodes = set(starts)
    constraints: list[tuple[int, int, int]] = []
    expanded: set[int] = set()
    frontier = set(starts)
    for _ in range(depth):
        following: set[int] = set()
        for parent in frontier:
            if parent == 0 or parent in expanded:
                continue
            first, second = transformed_moves(parent)
            constraints.append((parent, first, second))
            following.update((first, second))
            expanded.add(parent)
        nodes.update(following)
        frontier = following
    return nodes, constraints


def propagate(
    domains: dict[int, set[int]], constraints: list[tuple[int, int, int]]
) -> bool:
    changed = True
    while changed:
        changed = False
        for parent, first, second in constraints:
            triples = [
                (p, a, b)
                for p in domains[parent]
                for a in domains[first]
                for b in domains[second]
                if allowed(p, a, b)
            ]
            if not triples:
                return False
            supported = (
                {triple[0] for triple in triples},
                {triple[1] for triple in triples},
                {triple[2] for triple in triples},
            )
            for node, values in zip((parent, first, second), supported):
                narrowed = domains[node] & values
                if not narrowed:
                    return False
                if narrowed != domains[node]:
                    domains[node] = narrowed
                    changed = True
    return True


def satisfiable(
    domains: dict[int, set[int]], constraints: list[tuple[int, int, int]]
) -> bool:
    if not propagate(domains, constraints):
        return False
    undecided = [node for node, values in domains.items() if len(values) > 1]
    if not undecided:
        return True
    node = min(undecided, key=lambda value: len(domains[value]))
    for outcome in tuple(domains[node]):
        branch = {value: set(options) for value, options in domains.items()}
        branch[node] = {outcome}
        if satisfiable(branch, constraints):
            return True
    return False


def satisfying_assignment(
    domains: dict[int, set[int]], constraints: list[tuple[int, int, int]]
) -> dict[int, int] | None:
    """Return one satisfying assignment for diagnostics, if one exists."""
    if not propagate(domains, constraints):
        return None
    undecided = [node for node, values in domains.items() if len(values) > 1]
    if not undecided:
        return {node: next(iter(values)) for node, values in domains.items()}
    node = min(undecided, key=lambda value: len(domains[value]))
    for outcome in tuple(domains[node]):
        branch = {value: set(options) for value, options in domains.items()}
        branch[node] = {outcome}
        result = satisfying_assignment(branch, constraints)
        if result is not None:
            return result
    return None


def cnf_satisfiable(
    domains: dict[int, set[int]], constraints: list[tuple[int, int, int]]
) -> bool:
    """Solve the same finite outcome CSP through an exact two-bit CNF.

    For each node, the two Boolean variables mean WIN and LOSS; DRAW is the
    remaining assignment.  This is only a faster discovery backend.  An
    UNSAT result is not used as a theorem without a separately checked
    symbolic certificate.
    """
    nodes = tuple(domains)
    indices = {node: index for index, node in enumerate(nodes)}

    def win(node: int) -> int:
        return 2 * indices[node] + 1

    def loss(node: int) -> int:
        return 2 * indices[node] + 2

    clauses: list[set[int]] = []
    for parent, first, second in constraints:
        wp, lp = win(parent), loss(parent)
        wa, la = win(first), loss(first)
        wb, lb = win(second), loss(second)
        clauses.extend(
            (
                {-wp, la, lb},
                {-la, wp},
                {-lb, wp},
                {-lp, wa},
                {-lp, wb},
                {-wa, -wb, lp},
            )
        )

    for node, options in domains.items():
        w, ell = win(node), loss(node)
        clauses.append({-w, -ell})
        if D not in options:
            clauses.append({w, ell})
        if W not in options:
            clauses.append({-w})
        if L not in options:
            clauses.append({-ell})

    def simplify(
        current: list[set[int]], literal: int
    ) -> list[set[int]] | None:
        following: list[set[int]] = []
        opposite = -literal
        for clause in current:
            if literal in clause:
                continue
            if opposite not in clause:
                following.append(clause)
                continue
            reduced = clause - {opposite}
            if not reduced:
                return None
            following.append(reduced)
        return following

    def solve(current: list[set[int]]) -> bool:
        while True:
            units = [next(iter(clause)) for clause in current if len(clause) == 1]
            if not units:
                break
            for literal in units:
                reduced = simplify(current, literal)
                if reduced is None:
                    return False
                current = reduced
            if not current:
                return True

        if not current:
            return True

        signs: dict[int, set[bool]] = {}
        for clause in current:
            for literal in clause:
                signs.setdefault(abs(literal), set()).add(literal > 0)
        pure = [
            variable if next(iter(values)) else -variable
            for variable, values in signs.items()
            if len(values) == 1
        ]
        if pure:
            for literal in pure:
                reduced = simplify(current, literal)
                if reduced is None:
                    return False
                current = reduced
                if not current:
                    return True
            return solve(current)

        shortest = min(current, key=len)
        scores: dict[int, float] = {}
        for clause in current:
            weight = 1.0 / (len(clause) * len(clause))
            for literal in clause:
                variable = abs(literal)
                scores[variable] = scores.get(variable, 0.0) + weight
        variable = max((abs(literal) for literal in shortest), key=scores.__getitem__)
        for literal in (variable, -variable):
            reduced = simplify(current, literal)
            if reduced is not None and solve(reduced):
                return True
        return False

    return solve(clauses)


def boundary_locally_consistent(
    q: int,
    win_letter: str,
    witness_letter: str,
    depth: int,
    assume_smallest_draw: bool = False,
) -> bool:
    nodes, constraints = neighbourhood(q, depth)
    domains = {node: set(ALL) for node in nodes}
    if 0 in domains:
        domains[0] = {L}
    first, second = transformed_moves(q)
    children = {"A": first, "B": second}
    win = children[win_letter]
    draw = children["B" if win_letter == "A" else "A"]
    if win == 0 or draw == 0:
        return False

    def force(node: int, outcome: int) -> bool:
        domains[node].intersection_update((outcome,))
        return bool(domains[node])

    if not force(q, D) or not force(win, W) or not force(draw, D):
        return False
    if assume_smallest_draw:
        for node in nodes:
            if node < q:
                domains[node].discard(D)
                if not domains[node]:
                    return False

    witness_children = dict(zip(("A", "B"), transformed_moves(win)))
    witness = witness_children[witness_letter]
    if not force(witness, L):
        return False
    low_wins = set(transformed_moves(witness))
    for low in low_wins:
        if not force(low, W):
            return False

    # A lower-height WIN cannot be a child of any known DRAW node if the
    # original boundary WIN had globally minimum proof height.
    for parent, child_a, child_b in constraints:
        if child_a in low_wins or child_b in low_wins:
            domains[parent].discard(D)
            if not domains[parent]:
                return False
        if parent < q and (child_a == win or child_b == win):
            domains[parent].discard(D)
            if not domains[parent]:
                return False
    return satisfiable(domains, constraints)


def minimum_core_draw_locally_consistent(q: int, depth: int) -> bool:
    """Test a bounded neighbourhood under the minimum-core DRAW hypothesis."""
    minimum_core = constant_tail_coordinates(q)[0]
    nodes, constraints = neighbourhood(q, depth)
    domains = {node: set(ALL) for node in nodes}
    if 0 in domains:
        domains[0] = {L}
    domains[q] = {D}
    for node in nodes:
        if node == 0:
            continue
        if constant_tail_coordinates(node)[0] < minimum_core:
            domains[node].discard(D)
            if not domains[node]:
                return False
    return satisfiable(domains, constraints)


def minimum_source_lift_locally_consistent(source: int, depth: int) -> bool:
    """Test the canonical lift under the globally minimum source hypothesis."""
    q = constant_tail_state(
        embedded_original_state(source),
        1,
        source_A_selecting_tail_bit(source),
    )
    nodes, constraints = neighbourhood(q, depth)
    domains = {node: set(ALL) for node in nodes}
    if 0 in domains:
        domains[0] = {L}
    domains[q] = {D}
    for node in nodes:
        if node == 0:
            continue
        if constant_tail_source_coordinates(node)[0] < source:
            domains[node].discard(D)
            if not domains[node]:
                return False
    return satisfiable(domains, constraints)


def d2_loss_lift_locally_consistent(
    t: int, phase: int, depth: int, forbid_lower_boundary: bool
) -> tuple[bool, tuple[int, ...]]:
    """Test the unresolved direct-DRAW lift in the marked D=2 row.

    This is a bounded discovery test, not a proof.  The marked outcomes are
    b,q WIN and y LOSS.  The exact returned lift w is forced DRAW.  If
    ``forbid_lower_boundary`` is true, no child of y may have a DRAW parent;
    that is the consequence required when b is a globally minimum-height
    DRAW-boundary endpoint.
    """

    g = phase
    b = constant_tail_state(27 * embedded_original_state(t), 2, g)
    q = transformed_A(b)
    y = transformed_B(b)
    numerator = 9 * embedded_original_state(b) + 1 - 2 * g
    valuation = v2(numerator)
    if valuation != 1:
        raise AssertionError((t, g, valuation))
    odd_coefficient = numerator >> valuation
    w = inverse_F((odd_coefficient - 1) // 2)
    if w is None:
        raise AssertionError((t, g, odd_coefficient))

    roots = {b, q, y, w}
    nodes, constraints = multi_neighbourhood(roots, depth)
    domains = {node: set(ALL) for node in nodes}
    if 0 in domains:
        domains[0] = {L}
    for node, outcome in ((b, W), (q, W), (y, L), (w, D)):
        domains[node] = {outcome}

    low_wins = set(transformed_moves(y))
    if forbid_lower_boundary:
        for parent, child_a, child_b in constraints:
            if child_a in low_wins or child_b in low_wins:
                domains[parent].discard(D)
                if not domains[parent]:
                    return False, (b, q, y, w, *sorted(low_wins))
    return cnf_satisfiable(domains, constraints), (
        b,
        q,
        y,
        w,
        *sorted(low_wins),
    )


def residual_A_source(source: int) -> tuple[int, int] | None:
    """Return the final A-selecting ``(x,e)`` reached in Sections 26--27."""
    returned = transformed_B(transformed_A(source))
    common = transformed_A(transformed_A(returned))
    current = transformed_B(common)
    phase = source_A_selecting_tail_bit(common)
    if current < source:
        return None
    for _ in range(3):
        if phase == source_A_selecting_tail_bit(current):
            return current, phase
        letter, valuation, following = source_boundary_transition(current, phase)
        if letter != "B" or valuation != 2 or following < source:
            return None
        current = following
        phase = 1 - phase
    return None


def factor_fork_locally_consistent(
    source: int,
    depth: int,
    minimum_boundary_height: bool = False,
    use_cnf: bool = False,
) -> tuple[bool, tuple[int, int, int]] | None:
    """Test the exact surviving factor fork of Sections 28--29."""
    reached = residual_A_source(source)
    if reached is None:
        return None
    x, phase = reached
    coefficient = embedded_original_state(x)
    opposite = 1 - phase
    signed = 9 * coefficient + 1 - 2 * phase
    lower_exponent = v2(signed) - 1
    factor_coefficient = signed >> v2(signed)
    factor_source, power_of_three, _, _ = constant_tail_source_coordinates(
        constant_tail_state(factor_coefficient, 1, opposite)
    )
    if power_of_three != 0:
        raise AssertionError((source, x))
    if factor_source < source or lower_exponent not in (1, 2, 3):
        return None

    p = constant_tail_state(coefficient, 1, phase)
    u = constant_tail_state(coefficient, 2, phase)
    v = transformed_A(p)
    b = transformed_B(p)
    f = transformed_A(u)
    roots = {p, u, v, b, f}
    nodes, constraints = multi_neighbourhood(roots, depth)
    domains = {node: set(ALL) for node in nodes}
    if 0 in domains:
        domains[0] = {L}
    forced = {p: W, u: D, v: L, b: W, f: D}
    for node, outcome in forced.items():
        domains[node] = {outcome}
    for node in nodes:
        if node == 0:
            continue
        if constant_tail_source_coordinates(node)[0] < source:
            domains[node].discard(D)
            if not domains[node]:
                return False, (x, factor_source, lower_exponent)
    if minimum_boundary_height:
        # P is the WIN child of the DRAW parent in the second alternative of
        # O(x,e), and V is its unique LOSS child.  If P is chosen with global
        # minimum boundary height, both children of V are strictly lower WINs
        # and therefore cannot themselves be children of a DRAW.
        lower_wins = set(transformed_moves(v))
        for parent, child_a, child_b in constraints:
            if child_a in lower_wins or child_b in lower_wins:
                domains[parent].discard(D)
                if not domains[parent]:
                    return False, (x, factor_source, lower_exponent)
    solver = cnf_satisfiable if use_cnf else satisfiable
    return solver(domains, constraints), (x, factor_source, lower_exponent)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=4096)
    parser.add_argument("--depth", type=int, default=7)
    parser.add_argument("--smallest-draw", action="store_true")
    parser.add_argument("--minimum-core", action="store_true")
    parser.add_argument("--minimum-source-lifts", action="store_true")
    parser.add_argument("--factor-forks", action="store_true")
    parser.add_argument("--minimum-boundary-height", action="store_true")
    parser.add_argument("--d2-loss-lifts", action="store_true")
    parser.add_argument("--cnf", action="store_true")
    parser.add_argument("--max-exponent", type=int, default=8)
    args = parser.parse_args()

    if args.d2_loss_lifts:
        survivors = []
        rejected = []
        for t in range(1, args.limit + 1):
            for phase in (0, 1):
                consistent, coordinates = d2_loss_lift_locally_consistent(
                    t,
                    phase,
                    args.depth,
                    forbid_lower_boundary=args.minimum_boundary_height,
                )
                row = (t, phase, *coordinates)
                (survivors if consistent else rejected).append(row)
        print(
            f"D=2 direct LOSS-lifts: sources <= {args.limit:,}; "
            f"depth={args.depth}; forbid-lower-boundary="
            f"{args.minimum_boundary_height}"
        )
        print(f"rejected: {len(rejected):,}; survivors: {len(survivors):,}")
        print(f"first rejected: {rejected[:32]}")
        print(f"first survivors: {survivors[:64]}")
        return

    if args.factor_forks:
        surviving = []
        rejected = []
        for source in range(1, args.limit + 1):
            if source % 128 not in {10, 31, 32, 53, 74, 95, 96, 117}:
                continue
            result = factor_fork_locally_consistent(
                source,
                args.depth,
                minimum_boundary_height=args.minimum_boundary_height,
                use_cnf=args.cnf,
            )
            if result is None:
                continue
            consistent, coordinates = result
            row = (source,) + coordinates
            (surviving if consistent else rejected).append(row)
        print(
            f"final factor forks: sources <= {args.limit:,}; depth={args.depth}"
        )
        print(f"rejected: {len(rejected):,}; survivors: {len(surviving):,}")
        print(f"first rejected: {rejected[:64]}")
        print(f"first survivors: {surviving[:128]}")
        return

    if args.minimum_source_lifts:
        surviving = []
        rejected = []
        for source in range(1, args.limit + 1):
            if minimum_source_lift_locally_consistent(source, args.depth):
                surviving.append(source)
            else:
                rejected.append(source)
        print(
            f"minimum-source canonical lifts: sources <= {args.limit:,}; "
            f"depth={args.depth}"
        )
        print(f"rejected: {len(rejected):,}; survivors: {len(surviving):,}")
        print(f"first rejected: {rejected[:64]}")
        print(f"first survivors: {surviving[:128]}")
        return

    if args.minimum_core:
        survivors: list[tuple[int, int, int, int]] = []
        rejected: list[tuple[int, int, int, int]] = []
        for coefficient in range(1, args.limit + 1, 2):
            for tail_bit in (0, 1):
                for exponent in range(1, args.max_exponent + 1):
                    q = constant_tail_state(coefficient, exponent, tail_bit)
                    if q == 1:
                        continue
                    row = (coefficient, exponent, tail_bit, q)
                    if minimum_core_draw_locally_consistent(q, args.depth):
                        survivors.append(row)
                    else:
                        rejected.append(row)
        print(
            f"minimum-core local search: coefficients <= {args.limit:,}; "
            f"exponents <= {args.max_exponent}; depth={args.depth}"
        )
        print(f"rejected: {len(rejected):,}; survivors: {len(survivors):,}")
        print(f"first rejected: {rejected[:32]}")
        print(f"first survivors: {survivors[:64]}")
        return

    counts: dict[tuple[str, str], int] = {}
    examples: dict[tuple[str, str], list[int]] = {}
    win_letters = ("B",) if args.smallest_draw else ("A", "B")
    for win_letter in win_letters:
        for witness_letter in ("A", "B"):
            surviving = []
            for q in range(1, args.limit + 1):
                if boundary_locally_consistent(
                    q,
                    win_letter,
                    witness_letter,
                    args.depth,
                    assume_smallest_draw=args.smallest_draw,
                ):
                    surviving.append(q)
            key = (win_letter, witness_letter)
            counts[key] = len(surviving)
            examples[key] = surviving[:32]

    print(f"limit: {args.limit:,}; forward depth: {args.depth}")
    print(f"smallest-DRAW assumption: {args.smallest_draw}")
    for key in counts:
        print(
            f"WIN child {key[0]}, designated LOSS child {key[1]}: "
            f"{counts[key]:,} locally consistent; examples={examples[key]}"
        )
    print("This bounded constraint search is computational evidence only.")


if __name__ == "__main__":
    main()
