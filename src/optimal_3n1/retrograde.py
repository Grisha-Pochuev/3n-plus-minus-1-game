"""Sound bounded retrograde analysis for the conjugated game.

Only positions whose status follows without assumptions about states above the
chosen limit are labeled WIN or LOSS. Every other position remains UNKNOWN.
The reverse graph is stored in compact CSR form to remain usable on a modest
laptop.
"""

from __future__ import annotations

from array import array
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
    resolved_at: array

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

    def proof_children(self, q: int) -> tuple[int, ...]:
        """Return children used by a finite proof of q's resolved outcome.

        For a proved WIN, one earlier proved LOSS child is returned.
        For a proved LOSS, both earlier proved WIN children are returned.
        UNKNOWN positions have no proof children.
        """
        outcome = self.outcome(q)
        if outcome == Outcome.UNKNOWN or q == 0:
            return ()

        children = transformed_moves(q)
        if outcome == Outcome.WIN:
            candidates = [
                child
                for child in children
                if child <= self.limit
                and self.outcome(child) == Outcome.LOSS
                and self.resolved_at[child] < self.resolved_at[q]
            ]
            if not candidates:
                raise AssertionError(f"missing finite WIN witness for q={q}")
            return (min(candidates, key=lambda child: self.resolved_at[child]),)

        if not all(
            child <= self.limit
            and self.outcome(child) == Outcome.WIN
            and self.resolved_at[child] < self.resolved_at[q]
            for child in children
        ):
            raise AssertionError(f"missing finite LOSS witnesses for q={q}")
        return children


def _build_reverse_csr(limit: int) -> tuple[array, array]:
    """Return (offsets, predecessors) for in-range edges in compact CSR form."""
    indegree = array("I", [0]) * (limit + 1)

    for q in range(1, limit + 1):
        for child in transformed_moves(q):
            if child <= limit:
                indegree[child] += 1

    offsets = array("I", [0]) * (limit + 2)
    for node in range(limit + 1):
        offsets[node + 1] = offsets[node] + indegree[node]

    predecessors = array("I", [0]) * offsets[limit + 1]
    cursor = array("I", offsets[:-1])

    for q in range(1, limit + 1):
        for child in transformed_moves(q):
            if child <= limit:
                position = cursor[child]
                predecessors[position] = q
                cursor[child] += 1

    return offsets, predecessors


def bounded_retrograde(limit: int) -> RetrogradeResult:
    """Classify all consequences provable inside 0..limit.

    Edges leaving the interval remain unresolved. Therefore a node is marked
    LOSS only when both of its actual children are already proved WIN, and a
    node is marked WIN as soon as one actual child is proved LOSS.
    """
    if limit < 0:
        raise ValueError("limit must be nonnegative")
    if limit >= 2**32 - 2:
        raise ValueError("this compact implementation requires limit < 2^32-2")

    outcomes = bytearray(limit + 1)
    remaining_not_win = bytearray(limit + 1)
    for q in range(1, limit + 1):
        remaining_not_win[q] = 2

    offsets, predecessors = _build_reverse_csr(limit)
    resolved_at = array("I", [0]) * (limit + 1)

    outcomes[0] = Outcome.LOSS
    resolved_at[0] = 1
    resolution_counter = 1
    queue: deque[int] = deque([0])

    while queue:
        child = queue.popleft()
        child_outcome = Outcome(outcomes[child])

        start = offsets[child]
        end = offsets[child + 1]
        for index in range(start, end):
            parent = predecessors[index]
            if outcomes[parent] != Outcome.UNKNOWN:
                continue

            if child_outcome == Outcome.LOSS:
                outcomes[parent] = Outcome.WIN
                resolution_counter += 1
                resolved_at[parent] = resolution_counter
                queue.append(parent)
            else:
                remaining_not_win[parent] -= 1
                if remaining_not_win[parent] == 0:
                    outcomes[parent] = Outcome.LOSS
                    resolution_counter += 1
                    resolved_at[parent] = resolution_counter
                    queue.append(parent)

    return RetrogradeResult(limit=limit, outcomes=outcomes, resolved_at=resolved_at)


def certified_finite_draw_kernel(result: RetrogradeResult) -> array:
    """Return a finite DRAW trap certified inside ``result.limit``.

    Remove every UNKNOWN node from which an UNKNOWN-only path can reach an
    edge above the cutoff. Every remaining UNKNOWN node has at least one
    remaining UNKNOWN child, while every other child is already proved WIN.
    Thus a nonempty returned set is a genuine finite DRAW certificate.

    An empty result excludes only this finite, boundary-independent kind of
    certificate at the chosen cutoff; it says nothing about unbounded draws.
    """
    limit = result.limit
    reaches_boundary = bytearray(limit + 1)
    queue: deque[int] = deque()

    for q in range(1, limit + 1):
        if result.outcomes[q] != Outcome.UNKNOWN:
            continue
        if any(child > limit for child in transformed_moves(q)):
            reaches_boundary[q] = 1
            queue.append(q)

    offsets, predecessors = _build_reverse_csr(limit)
    while queue:
        child = queue.popleft()
        for index in range(offsets[child], offsets[child + 1]):
            parent = predecessors[index]
            if (
                result.outcomes[parent] == Outcome.UNKNOWN
                and not reaches_boundary[parent]
            ):
                reaches_boundary[parent] = 1
                queue.append(parent)

    return array(
        "I",
        (
            q
            for q in range(1, limit + 1)
            if result.outcomes[q] == Outcome.UNKNOWN and not reaches_boundary[q]
        ),
    )


def iter_outcomes(result: RetrogradeResult) -> Iterable[tuple[int, Outcome]]:
    for q, value in enumerate(result.outcomes):
        yield q, Outcome(value)
