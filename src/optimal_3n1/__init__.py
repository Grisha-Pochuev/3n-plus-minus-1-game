"""Core tools for the optimal 3n±1 game."""

from .game import (
    decreasing_move,
    increasing_move,
    move_minus,
    move_plus,
    moves,
    odd_part,
    transformed_A,
    transformed_B,
    transformed_moves,
    alternating_suffix_remainder,
)

__all__ = [
    "alternating_suffix_remainder",
    "decreasing_move",
    "increasing_move",
    "move_minus",
    "move_plus",
    "moves",
    "odd_part",
    "transformed_A",
    "transformed_B",
    "transformed_moves",
]
