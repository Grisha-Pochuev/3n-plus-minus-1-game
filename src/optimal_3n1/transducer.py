"""Finite-state bit relations for the Gray-coordinate normal form.

Bits are read from least significant to most significant.  The transducer
below recognizes the graph of ``Gamma(g) = G(A(G^{-1}(g)))`` without first
decoding either Gray word to an integer.
"""

from __future__ import annotations

from typing import Final, TypeAlias


GrayAState: TypeAlias = tuple[int, int, int]

# A state at position i is (q_i, a_i, carry_{i+1}), where q_i and a_i are
# binary digits of q and A(q).  The carry belongs to
#
#     2 A(q) = 3q + (q mod 2).
#
# The low binary digits q_0 and A(q)_0 are guessed initially.  The accepting
# condition at the leading zero padding makes the guess unique.
GRAY_A_STATES: Final[tuple[GrayAState, ...]] = tuple(
    (q_bit, a_bit, carry)
    for q_bit in (0, 1)
    for a_bit in (0, 1)
    for carry in (0, 1)
)
GRAY_A_INITIAL_STATES: Final[tuple[GrayAState, ...]] = (
    (0, 0, 0),
    (0, 1, 0),
    (1, 0, 1),
    (1, 1, 1),
)
GRAY_A_ACCEPTING_STATE: Final[GrayAState] = (0, 0, 0)


def gray_A_transition(
    state: GrayAState, input_bit: int, output_bit: int
) -> GrayAState | None:
    """Take one LSB-first transition of the eight-state ``A`` relation.

    ``input_bit`` is a digit of ``G(q)`` and ``output_bit`` is the digit in
    the same position of ``G(A(q))``.  ``None`` means that the proposed pair
    of digits is incompatible with the multiplication carry.
    """
    if state not in GRAY_A_STATES:
        raise ValueError("invalid Gray-A state")
    if input_bit not in (0, 1) or output_bit not in (0, 1):
        raise ValueError("transducer letters must be bits")

    q_bit, a_bit, carry = state
    next_q_bit = q_bit ^ input_bit
    next_a_bit = a_bit ^ output_bit
    column_sum = next_q_bit + q_bit + carry
    if a_bit != column_sum & 1:
        return None
    return next_q_bit, next_a_bit, column_sum >> 1


def gray_A_transducer_path(
    input_gray: int, output_gray: int
) -> tuple[GrayAState, ...] | None:
    """Return the unique accepting state path for a proposed Gray pair.

    A leading zero column is included explicitly.  It rules out guessed low
    binary digits that would leave a nonzero infinite leading tail.
    """
    if input_gray < 0 or output_gray < 0:
        raise ValueError("Gray words must be nonnegative")

    width = max(input_gray.bit_length(), output_gray.bit_length()) + 1
    accepted: list[tuple[GrayAState, ...]] = []
    for initial in GRAY_A_INITIAL_STATES:
        state = initial
        path = [state]
        for position in range(width):
            state = gray_A_transition(
                state,
                (input_gray >> position) & 1,
                (output_gray >> position) & 1,
            )
            if state is None:
                break
            path.append(state)
        if state == GRAY_A_ACCEPTING_STATE:
            accepted.append(tuple(path))

    if len(accepted) > 1:
        raise AssertionError("the functional Gray-A relation was ambiguous")
    return accepted[0] if accepted else None


def gray_A_transducer_accepts(input_gray: int, output_gray: int) -> bool:
    """Whether the finite transducer accepts ``(input_gray, output_gray)``."""
    return gray_A_transducer_path(input_gray, output_gray) is not None
