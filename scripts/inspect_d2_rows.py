#!/usr/bin/env python3
"""Print exact symbolic coordinates at the marked D=2 return.

Discovery aid only.  It enumerates the v=8 marked high-return row, computes
the valuation-one returned lift over the marked LOSS child y, and prints the
ordinary source transition taken in the phase of the returned lift.  Since
the returned tail has length at least two, this phase is always B-selecting.
"""

from __future__ import annotations

import argparse

from optimal_3n1.game import (
    constant_tail_source_coordinates,
    constant_tail_state,
    embedded_original_state,
    inverse_F,
    source_boundary_transition,
    transformed_A,
    transformed_B,
    v2,
)
from optimal_3n1.retrograde import Outcome, bounded_retrograde


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--limit", type=int, default=64)
    parser.add_argument(
        "--retrograde-limit",
        type=int,
        default=0,
        help=(
            "optionally attach sound bounded outcomes/resolution times from "
            "0..N; states outside the window stay UNKNOWN"
        ),
    )
    args = parser.parse_args()
    retrograde = (
        bounded_retrograde(args.retrograde_limit)
        if args.retrograde_limit
        else None
    )

    def certificate(state: int) -> str:
        if retrograde is None or state > retrograde.limit:
            return "OUTSIDE"
        outcome = retrograde.outcome(state)
        if outcome == Outcome.UNKNOWN:
            return "UNKNOWN"
        return f"{outcome.name}@{retrograde.resolved_at[state]}"

    print(
        "t g b q y j w=(source,k,m,d) lift_phase transition "
        "B(w)-identity certificates[b,q,y,w,B(w),A(w)]"
    )
    for t in range(1, args.limit + 1):
        for g in (0, 1):
            b = constant_tail_state(27 * embedded_original_state(t), 2, g)
            q = transformed_A(b)
            y = transformed_B(b)
            numerator = 9 * embedded_original_state(b) + 1 - 2 * g
            j = v2(numerator)
            coefficient = numerator >> j
            w = inverse_F((coefficient - 1) // 2)
            assert w is not None and j == 1
            source, power, exponent, phase = constant_tail_source_coordinates(w)
            assert source == y and power == 0
            lift_phase = phase
            transition = source_boundary_transition(w, lift_phase)
            assert transition[0] == "B"
            assert transition[2] == transformed_B(w)
            bw = transformed_B(w)
            aq = transformed_A(q)
            identity = (
                "A2(q)"
                if bw == transformed_A(aq)
                else "B(A(q))"
                if bw == transformed_B(aq)
                else "OTHER"
            )
            assert identity != "OTHER"
            print(
                t,
                g,
                b,
                q,
                y,
                j,
                (source, power, exponent, phase),
                lift_phase,
                transition,
                identity,
                tuple(
                    certificate(state)
                    for state in (b, q, y, w, bw, transformed_A(w))
                ),
            )


if __name__ == "__main__":
    main()
