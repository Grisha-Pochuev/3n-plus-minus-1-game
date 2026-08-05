"""Exact arithmetic for the original and conjugated games."""

from __future__ import annotations

from typing import Tuple


SIDE_RELATION_EXCEPTIONAL_RESIDUES = frozenset({1, 3, 12, 14})


def v2(value: int) -> int:
    """Return the exponent of 2 dividing a positive integer."""
    if value <= 0:
        raise ValueError("v2 is defined here only for positive integers")
    return (value & -value).bit_length() - 1


def odd_part(value: int) -> int:
    """Remove all factors of 2 from a positive integer."""
    if value <= 0:
        raise ValueError("odd_part requires a positive integer")
    return value >> v2(value)


def _validate_original_state(n: int) -> None:
    if n <= 0 or n % 2 == 0:
        raise ValueError("the original game state must be a positive odd integer")


def move_plus(n: int) -> int:
    """Apply 3n+1 and remove all powers of 2."""
    _validate_original_state(n)
    return odd_part(3 * n + 1)


def move_minus(n: int) -> int:
    """Apply 3n-1 and remove all powers of 2."""
    _validate_original_state(n)
    if n == 1:
        raise ValueError("state 1 is terminal")
    return odd_part(3 * n - 1)


def moves(n: int) -> Tuple[int, int]:
    """Return the two legal children of a nonterminal original state."""
    _validate_original_state(n)
    if n == 1:
        return ()  # type: ignore[return-value]
    return move_minus(n), move_plus(n)


def decreasing_move(n: int) -> int:
    """Return the smaller legal child D(n)."""
    if n == 1:
        raise ValueError("state 1 is terminal")
    return min(moves(n))


def increasing_move(n: int) -> int:
    """Return the larger legal child U(n)."""
    if n == 1:
        raise ValueError("state 1 is terminal")
    return max(moves(n))


def F(m: int) -> int:
    """The injective map F(m)=ceil(3m/2)."""
    if m < 0:
        raise ValueError("m must be nonnegative")
    return (3 * m + 1) // 2


def alternating_suffix_length(m: int) -> int:
    """Length of the maximal alternating suffix of the binary expansion of m.

    For m=0 the length is defined as 0. For m>0 it is at least 1.
    """
    if m < 0:
        raise ValueError("m must be nonnegative")
    if m == 0:
        return 0

    length = 1
    current = m & 1
    m >>= 1
    while m:
        bit = m & 1
        if bit == current:
            break
        length += 1
        current = bit
        m >>= 1
    return length


def alternating_suffix_remainder(m: int) -> int:
    """Delete the maximal alternating binary suffix of m.

    Examples:
        0b1001 -> 0b10
        0b10101 -> 0
    """
    if m < 0:
        raise ValueError("m must be nonnegative")
    return m >> alternating_suffix_length(m)


def gray_code(value: int) -> int:
    """Return the reflected binary Gray code of a nonnegative integer."""
    if value < 0:
        raise ValueError("value must be nonnegative")
    return value ^ (value >> 1)


def inverse_gray_code(value: int) -> int:
    """Invert reflected binary Gray code on nonnegative integers."""
    if value < 0:
        raise ValueError("value must be nonnegative")
    result = 0
    while value:
        result ^= value
        value >>= 1
    return result


def alternating_suffix_remainder_via_gray(m: int) -> int:
    """Delete the alternating suffix by stripping a Gray-code bit block."""
    encoded = gray_code(m)
    stripped = encoded >> (v2(encoded + 1) + 1)
    return inverse_gray_code(stripped)


def alternating_word_value(length: int, leading_bit: int) -> int:
    """Return the value of an alternating binary word of fixed length.

    ``leading_bit`` is the most significant bit of the word. A leading zero
    is retained conceptually, which is useful when the word is appended to a
    nonempty binary prefix.
    """
    if length <= 0:
        raise ValueError("length must be positive")
    if leading_bit not in (0, 1):
        raise ValueError("leading_bit must be 0 or 1")
    if leading_bit == 0:
        return (1 << length) // 3
    return (1 << (length + 1)) // 3


def m_coordinates_children(m: int) -> Tuple[int, int]:
    """Children after writing the original odd state as n=2m+1."""
    if m < 0:
        raise ValueError("m must be nonnegative")
    if m == 0:
        return ()  # type: ignore[return-value]
    n = 2 * m + 1
    return tuple((child - 1) // 2 for child in moves(n))


def normal_form_children(m: int) -> Tuple[int, int]:
    """The same children as m_coordinates_children, via the binary normal form."""
    if m < 0:
        raise ValueError("m must be nonnegative")
    if m == 0:
        return ()  # type: ignore[return-value]
    return F(m), F(alternating_suffix_remainder(m))


def transformed_A(q: int) -> int:
    """Expanding branch A(q)=F(q)."""
    return F(q)


def transformed_B(q: int) -> int:
    """Contracting branch B(q)=R(F(q))."""
    if q < 0:
        raise ValueError("q must be nonnegative")
    return alternating_suffix_remainder(F(q))


def transformed_moves(q: int) -> Tuple[int, int]:
    """Children in the conjugated game; q=0 is terminal."""
    if q < 0:
        raise ValueError("q must be nonnegative")
    if q == 0:
        return ()  # type: ignore[return-value]
    return transformed_A(q), transformed_B(q)


def side_branch_relation(q: int) -> str | None:
    """Describe how consecutive side branches are related.

    Return ``"A"`` when ``B(A(q)) == A(B(q))``, ``"B"`` when
    ``B(A(q)) == B(B(q))``, and ``None`` for the four exceptional residue
    classes.  Whether an ordinary case is ``"A"`` or ``"B"`` can depend on
    higher bits, but the exceptional cases are exactly ``1,3,12,14 mod 16``.
    """
    if q < 0:
        raise ValueError("q must be nonnegative")
    side = transformed_B(q)
    next_side = transformed_B(transformed_A(q))
    if next_side == transformed_A(side):
        return "A"
    if next_side == transformed_B(side):
        return "B"
    if q % 16 not in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
        raise AssertionError(q)
    return None


def transformed_B_predecessors(r: int, limit: int) -> tuple[int, ...]:
    """Return all ``q <= limit`` satisfying ``B(q) == r``.

    The enumeration uses the exact alternating-suffix formula rather than a
    scan through all ``q``. Values outside the image of ``F`` are discarded.
    """
    if r < 0:
        raise ValueError("r must be nonnegative")
    if limit < 0:
        raise ValueError("limit must be nonnegative")

    largest_x = F(limit)
    predecessors: list[int] = [0] if r == 0 else []
    length = 1
    while True:
        if r == 0:
            x = alternating_word_value(length, 1)
        else:
            suffix = alternating_word_value(length, r & 1)
            x = (r << length) + suffix
        if x > largest_x:
            break
        q = inverse_F(x)
        if q is not None and q <= limit:
            predecessors.append(q)
        length += 1
    return tuple(predecessors)


def transformed_BBA(q: int) -> int:
    """The uniformly descending block ``B(B(A(q)))``."""
    if q < 0:
        raise ValueError("q must be nonnegative")
    return transformed_B(transformed_B(transformed_A(q)))


def transformed_BAB(q: int) -> int:
    """The uniformly descending block ``B(A(B(q)))``."""
    if q < 0:
        raise ValueError("q must be nonnegative")
    return transformed_B(transformed_A(transformed_B(q)))


def transformed_ABB(q: int) -> int:
    """The uniformly descending block ``A(B(B(q)))``."""
    if q < 0:
        raise ValueError("q must be nonnegative")
    return transformed_A(transformed_B(transformed_B(q)))


def inverse_F(y: int) -> int | None:
    """Return the unique x with F(x)=y, or None if y is not in the image."""
    if y < 0:
        raise ValueError("y must be nonnegative")
    residue = y % 3
    if residue == 0:
        return 2 * y // 3
    if residue == 2:
        return (2 * y - 1) // 3
    return None
