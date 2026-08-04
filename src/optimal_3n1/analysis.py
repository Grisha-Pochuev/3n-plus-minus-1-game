"""Small analysis helpers for experimental work."""

from __future__ import annotations

from dataclasses import dataclass

from .game import transformed_A, transformed_B
from .retrograde import Outcome, RetrogradeResult


@dataclass(frozen=True)
class SideBranchRun:
    start: int
    length: int
    stopping_q: int
    stopping_side_branch: int
    stopping_outcome: Outcome


def side_branch_run(result: RetrogradeResult, start: int, max_steps: int = 10000) -> SideBranchRun:
    """Follow A and count consecutive side branches B(A^k(start)) proved WIN.

    The run stops on LOSS, UNKNOWN, a state outside the retrograde window, or
    max_steps. It is an exploratory statistic, not a theorem about all q.
    """
    q = start
    length = 0
    for _ in range(max_steps):
        side = transformed_B(q)
        if side > result.limit:
            return SideBranchRun(start, length, q, side, Outcome.UNKNOWN)
        outcome = result.outcome(side)
        if outcome != Outcome.WIN:
            return SideBranchRun(start, length, q, side, outcome)
        length += 1
        q = transformed_A(q)
        if q > result.limit:
            return SideBranchRun(start, length, q, transformed_B(q), Outcome.UNKNOWN)
    return SideBranchRun(start, length, q, transformed_B(q), Outcome.UNKNOWN)
