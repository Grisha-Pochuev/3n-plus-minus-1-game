"""Exact arithmetic for the original and conjugated games."""

from __future__ import annotations

from typing import Tuple


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
