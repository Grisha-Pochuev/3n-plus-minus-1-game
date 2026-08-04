"""Sound bounded retrograde analysis for the conjugated game.

Only positions whose status follows without assumptions about states above the
chosen limit are labeled WIN or LOSS. Every other position remains UNKNOWN.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from enum import IntEnum
from typing import Iterable

from .game import transformed_moves


class Outcome(IntEnum):
    UNKNOWN = 0
    LOSS = 1
    WIN = 2


@dataclass(frozen=True)
class RetrogradeResult:
    limit: int
    outcomes: bytearray

    def outcome(self, q: int) -> Outcome:
        if not 0 <= q <= self.limit:
            raise IndexError(q)
        return Outcome(self.outcomes[q])

    def first_unknown(self) -> int | None:
        for q, value in enumerate(self.outcomes):
            if value == Outcome.UNKNOWN:
                return q
        return None

    def resolved_prefix_end(self) -> int:
        first = self.first_unknown()
        return self.limit if first is None else first - 1

    def counts(self) -> dict[str, int]:
        return {
            "loss": self.outcomes.count(Outcome.LOSS),
            "win": self.outcomes.count(Outcome.WIN),
            "unknown": self.outcomes.count(Outcome.UNKNOWN),
        }


def bounded_retrograde(limit: int) -> RetrogradeResult:
    """Classify all consequences provable inside 0..limit.

    Edges leaving the interval remain unresolved. Therefore a node is marked
    LOSS only when both of its actual children are already proved WIN, and a
    node is marked WIN as soon as one actual child is proved LOSS.
    """
    if limit < 0:
        raise ValueError("limit must be nonnegative")

    outcomes = bytearray(limit + 1)
    remaining_not_win = bytearray([0]) * (limit + 1)
    predecessors: list[list[int]] = [[] for _ in range(limit + 1)]

    for q in range(1, limit + 1):
        children = transformed_moves(q)
        remaining_not_win[q] = len(children)
        for child in children:
            if child <= limit:
                predecessors[child].append(q)

    outcomes[0] = Outcome.LOSS
    queue: deque[int] = deque([0])

    while queue:
        child = queue.popleft()
        child_outcome = Outcome(outcomes[child])

        for parent in predecessors[child]:
            if outcomes[parent] != Outcome.UNKNOWN:
                continue

            if child_outcome == Outcome.LOSS:
                outcomes[parent] = Outcome.WIN
                queue.append(parent)
            else:
                remaining_not_win[parent] -= 1
                if remaining_not_win[parent] == 0:
                    outcomes[parent] = Outcome.LOSS
                    queue.append(parent)

    return RetrogradeResult(limit=limit, outcomes=outcomes)


def iter_outcomes(result: RetrogradeResult) -> Iterable[tuple[int, Outcome]]:
    for q, value in enumerate(result.outcomes):
        yield q, Outcome(value)
