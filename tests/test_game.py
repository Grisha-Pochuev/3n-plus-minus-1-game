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
    constant_tail_children,
    constant_tail_state,
    dyadic_minus_one_children,
    dyadic_minus_one_state,
    exceptional_side_branch_values,
    gray_code,
    increasing_move,
    inverse_F,
    inverse_gray_code,
    long_side_branch_value,
    m_coordinates_children,
    normal_form_children,
    odd_part,
    side_branch_relation,
    transformed_A,
    transformed_ABB,
    transformed_B,
    transformed_BAB,
    transformed_BBA,
    transformed_B_predecessors,
    v2,
)
from optimal_3n1.transducer import (  # noqa: E402
    GRAY_A_ACCEPTING_STATE,
    GRAY_A_STATES,
    gray_A_transducer_accepts,
    gray_A_transducer_path,
    gray_A_transition,
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

    def test_gray_A_eight_state_transducer(self) -> None:
        self.assertEqual(len(GRAY_A_STATES), 8)
        for state in GRAY_A_STATES:
            for input_bit in (0, 1):
                for output_bit in (0, 1):
                    following = gray_A_transition(state, input_bit, output_bit)
                    self.assertTrue(following is None or following in GRAY_A_STATES)

        for q in range(256):
            input_gray = gray_code(q)
            expected = gray_code(transformed_A(q))
            path = gray_A_transducer_path(input_gray, expected)
            self.assertIsNotNone(path)
            self.assertEqual(path[-1], GRAY_A_ACCEPTING_STATE)  # type: ignore[index]
            for proposed in range(512):
                self.assertEqual(
                    gray_A_transducer_accepts(input_gray, proposed),
                    proposed == expected,
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

    def test_every_three_move_two_B_block_decreases(self) -> None:
        for q in range(1, 100000):
            self.assertLess(transformed_BBA(q), q)
            self.assertLess(transformed_BAB(q), q)
            self.assertLess(transformed_ABB(q), q)

    def test_coarse_exception_return_cycle(self) -> None:
        q = 17
        for letter in "ABAAAAAAABBB":
            q = transformed_A(q) if letter == "A" else transformed_B(q)
        self.assertEqual(q, 17)

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
            if relation is not None:
                suffix_length = alternating_suffix_length(transformed_A(q))
                remainder = transformed_B(q)
                expected_A_residues = {0, 3} if suffix_length == 1 else {1, 2}
                self.assertIn(suffix_length, {1, 2})
                self.assertEqual(
                    relation == "A", remainder % 4 in expected_A_residues
                )

    def test_exceptional_side_branch_formulas(self) -> None:
        for q in range(1, 10000):
            values = exceptional_side_branch_values(q)
            if q % 16 not in {1, 3, 12, 14}:
                self.assertIsNone(values)
                continue
            self.assertEqual(
                values,
                (transformed_B(q), transformed_B(transformed_A(q))),
            )

    def test_long_side_branch_formula(self) -> None:
        for q in range(1, 100000):
            value = long_side_branch_value(q)
            self.assertEqual(
                value is not None,
                alternating_suffix_length(transformed_A(q)) >= 3,
            )
            if value is not None:
                self.assertEqual(value, transformed_B(transformed_A(q)))

    def test_dyadic_minus_one_recurrence(self) -> None:
        for odd_coefficient in range(1, 1000, 2):
            for exponent in range(3, 16):
                state = dyadic_minus_one_state(odd_coefficient, exponent)
                self.assertEqual(
                    dyadic_minus_one_children(odd_coefficient, exponent),
                    (transformed_A(state), transformed_B(state)),
                )

                for tail_bit in (0, 1):
                    state = constant_tail_state(
                        odd_coefficient, exponent, tail_bit
                    )
                    self.assertEqual(
                        constant_tail_children(
                            odd_coefficient, exponent, tail_bit
                        ),
                        (transformed_A(state), transformed_B(state)),
                    )

            first = dyadic_minus_one_state(odd_coefficient, 1)
            second = dyadic_minus_one_state(odd_coefficient, 2)
            self.assertEqual(transformed_B(first), transformed_B(second))
            self.assertEqual(
                transformed_A(first),
                dyadic_minus_one_state(3 * odd_coefficient, 0),
            )
            self.assertEqual(
                transformed_A(second),
                dyadic_minus_one_state(3 * odd_coefficient, 1),
            )


    def test_constant_tail_boundary(self) -> None:
        for odd_coefficient in range(1, 1000, 2):
            for tail_bit in (0, 1):
                first = constant_tail_state(odd_coefficient, 1, tail_bit)
                second = constant_tail_state(odd_coefficient, 2, tail_bit)
                self.assertEqual(transformed_B(first), transformed_B(second))

                expanding = transformed_A(first)
                signed_value = 3 * odd_coefficient + 1 - 2 * tail_bit
                exponent = v2(signed_value)
                coefficient = signed_value >> exponent
                self.assertEqual(
                    expanding,
                    constant_tail_state(
                        coefficient, exponent, 1 - tail_bit
                    ),
                )

    def test_height_one_arithmetic(self) -> None:
        for q in range(1, 100000):
            if transformed_B(q) == 0:
                self.assertIn(q % 16, {1, 3, 12, 14})
            if transformed_B(transformed_A(q)) == 0:
                self.assertGreater(transformed_B(q), 0)
                self.assertEqual(transformed_B(transformed_B(q)), 0)

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
        for n in range(3, 100000, 2):
            d = decreasing_move(n)
            if d == 1:
                continue
            self.assertLess(decreasing_move(d), n)
            self.assertLess(decreasing_move(increasing_move(d)), n)

    def test_one_player_decreasing_strategy_can_cycle(self) -> None:
        self.assertEqual(increasing_move(5), 7)
        self.assertEqual(decreasing_move(7), 5)


if __name__ == "__main__":
    unittest.main()
