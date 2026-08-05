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
    constant_tail_coordinates,
    constant_tail_coefficient_source,
    constant_tail_state,
    dyadic_minus_one_children,
    dyadic_minus_one_state,
    embedded_original_state,
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
    source_A_selecting_tail_bit,
    source_boundary_transition,
    transformed_A,
    transformed_ABB,
    transformed_B,
    transformed_BAB,
    transformed_BBA,
    transformed_B_predecessors,
    transformed_moves,
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

    def test_constant_tail_coordinates_and_boundary_core_drop(self) -> None:
        for state in range(1, 100000):
            coefficient, exponent, tail_bit = constant_tail_coordinates(state)
            self.assertEqual(
                constant_tail_state(coefficient, exponent, tail_bit),
                state,
            )
            self.assertGreaterEqual(exponent, 1)

        for odd_coefficient in range(1, 1000, 2):
            for tail_bit in (0, 1):
                first = constant_tail_state(odd_coefficient, 1, tail_bit)
                common_child = transformed_B(first)
                if common_child > 0:
                    child_coefficient, _, _ = constant_tail_coordinates(
                        common_child
                    )
                    if odd_coefficient == 1 and tail_bit == 0:
                        self.assertEqual(child_coefficient, odd_coefficient)
                    else:
                        self.assertLess(child_coefficient, odd_coefficient)

                signed_value = 3 * odd_coefficient + 1 - 2 * tail_bit
                exponent = v2(signed_value)
                expanding_coefficient = signed_value >> exponent
                if exponent >= 2:
                    if odd_coefficient == 1 and tail_bit == 0:
                        self.assertEqual(
                            expanding_coefficient, odd_coefficient
                        )
                    else:
                        self.assertLess(
                            expanding_coefficient, odd_coefficient
                        )

    def test_constant_tail_second_boundary_fork(self) -> None:
        for odd_coefficient in range(1, 1000, 2):
            for tail_bit in (0, 1):
                signed_value = 3 * odd_coefficient + 1 - 2 * tail_bit
                if v2(signed_value) != 1:
                    continue

                intermediate_coefficient = signed_value // 2
                intermediate = constant_tail_state(
                    intermediate_coefficient, 1, 1 - tail_bit
                )
                second_signed_value = 9 * odd_coefficient + 1 - 2 * tail_bit
                second_valuation = v2(second_signed_value)
                second_coefficient = (
                    second_signed_value >> second_valuation
                )

                self.assertEqual(
                    constant_tail_coordinates(transformed_A(intermediate)),
                    (
                        second_coefficient,
                        second_valuation - 1,
                        tail_bit,
                    ),
                )

                if second_valuation >= 3:
                    self.assertEqual(
                        constant_tail_coordinates(transformed_B(intermediate)),
                        (
                            second_coefficient,
                            second_valuation - 2,
                            tail_bit,
                        ),
                    )
                elif transformed_B(intermediate) > 0:
                    contracting_coefficient, _, _ = constant_tail_coordinates(
                        transformed_B(intermediate)
                    )
                    self.assertLess(
                        contracting_coefficient, odd_coefficient
                    )

                if second_valuation >= 4:
                    self.assertLess(second_coefficient, odd_coefficient)
                elif second_valuation == 3 and odd_coefficient > 1:
                    common_child = transformed_B(
                        constant_tail_state(
                            second_coefficient, 1, tail_bit
                        )
                    )
                    if common_child > 0:
                        common_coefficient, _, _ = constant_tail_coordinates(
                            common_child
                        )
                        self.assertLess(
                            common_coefficient, odd_coefficient
                        )

    def test_divisible_coefficient_draw_frame_identities(self) -> None:
        for base_coefficient in range(1, 100, 2):
            coefficient = 3 * base_coefficient
            for tail_bit in (0, 1):
                for exponent in range(2, 10):
                    state = constant_tail_state(
                        coefficient, exponent, tail_bit
                    )
                    lower_parent = constant_tail_state(
                        base_coefficient, exponent + 1, tail_bit
                    )
                    upper_parent = constant_tail_state(
                        base_coefficient, exponent + 2, tail_bit
                    )
                    self.assertIn(state, transformed_moves(lower_parent))
                    self.assertIn(state, transformed_moves(upper_parent))

                    lower_sibling = next(
                        child
                        for child in transformed_moves(lower_parent)
                        if child != state
                    )
                    upper_sibling = next(
                        child
                        for child in transformed_moves(upper_parent)
                        if child != state
                    )
                    for child in transformed_moves(state):
                        self.assertTrue(
                            child in transformed_moves(lower_sibling)
                            or child in transformed_moves(upper_sibling)
                        )

    def test_constant_tail_coefficient_source_conjugacy(self) -> None:
        for source in range(10000):
            original = embedded_original_state(source)
            self.assertEqual(constant_tail_coefficient_source(original), (source, 0))
            if source > 0:
                original_children = {
                    embedded_original_state(child)
                    for child in transformed_moves(source)
                }
                self.assertEqual(
                    original_children,
                    {odd_part(3 * original - 1), odd_part(3 * original + 1)},
                )

                selecting_tail = source_A_selecting_tail_bit(source)
                selected = source_boundary_transition(source, selecting_tail)
                other = source_boundary_transition(source, 1 - selecting_tail)
                self.assertEqual(selected, ("A", 1, transformed_A(source)))
                self.assertEqual(other[0], "B")
                self.assertGreaterEqual(other[1], 2)
                self.assertEqual(other[2], transformed_B(source))

        for odd_coefficient in range(1, 10000, 2):
            source, exponent_of_three = constant_tail_coefficient_source(
                odd_coefficient
            )
            self.assertEqual(
                odd_coefficient,
                (3**exponent_of_three) * embedded_original_state(source),
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
