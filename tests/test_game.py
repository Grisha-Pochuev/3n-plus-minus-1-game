import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from optimal_3n1.game import (  # noqa: E402
    F,
    alternating_suffix_length,
    alternating_suffix_remainder,
    alternating_suffix_remainder_via_gray,
    alternating_word_value,
    decreasing_move,
    gray_code,
    inverse_F,
    inverse_gray_code,
    m_coordinates_children,
    normal_form_children,
    odd_part,
    side_branch_relation,
    transformed_A,
    transformed_B,
    transformed_BBA,
    transformed_B_predecessors,
    v2,
)


class GameArithmeticTests(unittest.TestCase):
    def test_odd_part(self) -> None:
        self.assertEqual(odd_part(40), 5)
        self.assertEqual(odd_part(7), 7)

    def test_alternating_suffix_examples(self) -> None:
        self.assertEqual(alternating_suffix_length(0b1001), 2)
        self.assertEqual(alternating_suffix_remainder(0b1001), 0b10)
        self.assertEqual(alternating_suffix_remainder(0b10101), 0)
        self.assertEqual(alternating_suffix_remainder(0b11101), 0b11)

    def test_alternating_word_value(self) -> None:
        self.assertEqual(alternating_word_value(1, 0), 0b0)
        self.assertEqual(alternating_word_value(4, 0), 0b0101)
        self.assertEqual(alternating_word_value(1, 1), 0b1)
        self.assertEqual(alternating_word_value(5, 1), 0b10101)

    def test_gray_normal_form_for_R(self) -> None:
        for value in range(10000):
            encoded = gray_code(value)
            self.assertEqual(inverse_gray_code(encoded), value)
            self.assertEqual(
                alternating_suffix_remainder_via_gray(value),
                alternating_suffix_remainder(value),
            )
            stripped = encoded >> (v2(encoded + 1) + 1)
            self.assertEqual(
                stripped, gray_code(alternating_suffix_remainder(value))
            )

    def test_normal_form(self) -> None:
        for m in range(1, 10000):
            self.assertEqual(sorted(m_coordinates_children(m)), sorted(normal_form_children(m)))

    def test_B_strictly_decreases(self) -> None:
        for q in range(1, 10000):
            self.assertLess(transformed_B(q), q)

    def test_BBA_strictly_decreases(self) -> None:
        for q in range(1, 100000):
            self.assertLess(transformed_BBA(q), q)

    def test_side_branch_relation(self) -> None:
        for q in range(1, 10000):
            relation = side_branch_relation(q)
            self.assertEqual(relation is None, q % 16 in {1, 3, 12, 14})
            next_side = transformed_B(transformed_A(q))
            if relation == "A":
                self.assertEqual(next_side, transformed_A(transformed_B(q)))
            elif relation == "B":
                self.assertEqual(next_side, transformed_B(transformed_B(q)))
            else:
                self.assertIsNotNone(side_branch_relation(transformed_A(q)))

    def test_B_predecessor_parameterization(self) -> None:
        limit = 2000
        actual: dict[int, list[int]] = {}
        for q in range(limit + 1):
            actual.setdefault(transformed_B(q), []).append(q)
        for r in range(limit + 1):
            self.assertEqual(
                transformed_B_predecessors(r, limit), tuple(actual.get(r, ()))
            )

    def test_inverse_F(self) -> None:
        for q in range(10000):
            self.assertEqual(inverse_F(F(q)), q)
        for y in range(1, 10000, 3):
            self.assertIsNone(inverse_F(y))

    def test_descent_blocks(self) -> None:
        from optimal_3n1.game import increasing_move

        for n in range(3, 100000, 2):
            d = decreasing_move(n)
            if d == 1:
                continue
            self.assertLess(decreasing_move(d), n)
            self.assertLess(decreasing_move(increasing_move(d)), n)


if __name__ == "__main__":
    unittest.main()
