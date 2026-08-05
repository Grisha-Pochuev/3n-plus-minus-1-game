import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from optimal_3n1.game import (  # noqa: E402
    F,
    SIDE_RELATION_EXCEPTIONAL_RESIDUES,
    alternating_suffix_length,
    alternating_suffix_remainder,
    alternating_suffix_remainder_via_gray,
    alternating_word_value,
    decreasing_move,
    constant_tail_children,
    constant_tail_coordinates,
    constant_tail_coefficient_source,
    constant_tail_source_coordinates,
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

    def test_canonical_side_return_token(self) -> None:
        for q in range(1, 100000):
            expanding = transformed_A(q)
            contracting = transformed_B(q)
            returned = transformed_B(expanding)

            if q % 16 in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
                self.assertEqual(
                    constant_tail_source_coordinates(returned)[:2],
                    (contracting, 0),
                )
            else:
                self.assertIn(returned, transformed_moves(expanding))
                self.assertIn(returned, transformed_moves(contracting))

    def test_exceptional_side_return_adjacent_lift(self) -> None:
        for q in range(1, 100000):
            if q % 16 not in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
                continue
            loss_source = transformed_B(q)
            draw_child = transformed_A(q)
            lower_lift = transformed_B(draw_child)
            upper_lift = transformed_A(draw_child)
            lower_coordinates = constant_tail_source_coordinates(lower_lift)
            upper_coordinates = constant_tail_source_coordinates(upper_lift)

            self.assertEqual(lower_coordinates[:2], (loss_source, 0))
            self.assertEqual(upper_coordinates[:2], (loss_source, 0))
            self.assertEqual(upper_coordinates[2], lower_coordinates[2] + 1)
            self.assertEqual(upper_coordinates[3], lower_coordinates[3])

            if lower_coordinates[2] == 2:
                coefficient = embedded_original_state(loss_source)
                phase = lower_coordinates[3]
                boundary_parent = (
                    2 * upper_lift + phase - 1
                ) // 3
                self.assertEqual(coefficient % 3, 1 + phase)
                self.assertEqual(
                    transformed_moves(boundary_parent),
                    (upper_lift, lower_lift),
                )

    def test_canonical_A_streak_side_returns(self) -> None:
        small_exceptional_rows = set()
        for source in range(1, 100000):
            ray = [source]
            for _ in range(5):
                ray.append(transformed_A(ray[-1]))

            phase = source_A_selecting_tail_bit(source)
            for index in range(4):
                expected_phase = phase ^ (index % 2)
                if source_A_selecting_tail_bit(ray[index]) != expected_phase:
                    break
                if (
                    source_A_selecting_tail_bit(ray[index + 1])
                    != 1 - expected_phase
                ):
                    break

                lifted = constant_tail_state(
                    embedded_original_state(ray[index]),
                    1,
                    expected_phase,
                )
                self.assertEqual(transformed_B(lifted), ray[index + 2])

                preceding_win = ray[index + 1]
                if preceding_win % 16 in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
                    loss_token = transformed_B(preceding_win)
                    returned = transformed_B(transformed_A(preceding_win))
                    self.assertLess(loss_token, source)
                    self.assertEqual(
                        constant_tail_source_coordinates(returned)[:2],
                        (loss_token, 0),
                    )
                    upper_returned = transformed_A(
                        transformed_A(preceding_win)
                    )
                    upper_coordinates = constant_tail_source_coordinates(
                        upper_returned
                    )
                    lower_coordinates = constant_tail_source_coordinates(
                        returned
                    )
                    self.assertEqual(upper_coordinates[:2], (loss_token, 0))
                    self.assertEqual(
                        upper_coordinates[2],
                        lower_coordinates[2] + 1,
                    )
                    self.assertEqual(
                        upper_coordinates[3],
                        lower_coordinates[3],
                    )
                    if source < 12:
                        small_exceptional_rows.add(
                            (source, index, preceding_win, loss_token)
                        )

        self.assertEqual(
            small_exceptional_rows,
            {
                (4, 2, 14, 0),
                (6, 1, 14, 0),
                (9, 0, 14, 0),
                (11, 0, 17, 1),
            },
        )

    def test_post_canonical_B_run_contracts_in_nine_steps(self) -> None:
        for minimum_source in range(10, 5000):
            for source in (minimum_source, 2 * minimum_source - 1):
                current = source
                for _ in range(5):
                    returned = current
                    for _ in range(9):
                        returned = transformed_B(returned)
                    self.assertLess(returned, minimum_source)
                    current = transformed_A(current)

    def test_canonical_A_to_B_switch_rank_geometry(self) -> None:
        observed_valuations = set()
        for source in range(1, 100000):
            phase = source_A_selecting_tail_bit(source)
            selected_source = transformed_A(source)
            opposite_phase = 1 - phase
            if (
                opposite_phase
                == source_A_selecting_tail_bit(selected_source)
            ):
                continue

            letter, valuation, returned_source = source_boundary_transition(
                selected_source, opposite_phase
            )
            observed_valuations.add(valuation)
            self.assertEqual(letter, "B")
            self.assertEqual(
                returned_source,
                transformed_B(selected_source),
            )
            self.assertNotIn(
                source % 16,
                SIDE_RELATION_EXCEPTIONAL_RESIDUES,
            )
            self.assertIn(
                returned_source,
                transformed_moves(transformed_B(source)),
            )

            lift = constant_tail_state(
                embedded_original_state(source), 1, phase
            )
            self.assertEqual(transformed_B(lift), returned_source)

            if valuation >= 3:
                self.assertLess(returned_source, source)
            else:
                self.assertEqual(valuation, 2)

        self.assertIn(2, observed_valuations)
        self.assertIn(3, observed_valuations)
        self.assertTrue(any(value >= 10 for value in observed_valuations))

    def test_arbitrarily_long_phase_only_AB_prefixes(self) -> None:
        for pair_count in range(1, 25):
            multiplier = 2 if pair_count % 2 == 0 else 4
            coefficient = multiplier * 8**pair_count - 1
            source, power_of_three = constant_tail_coefficient_source(
                coefficient
            )
            self.assertEqual(power_of_three, 0)
            self.assertEqual(embedded_original_state(source), coefficient)

            phase = 0
            for _ in range(pair_count):
                letter, valuation, source = source_boundary_transition(
                    source, phase
                )
                self.assertEqual((letter, valuation), ("A", 1))
                phase = 1 - phase
                letter, valuation, source = source_boundary_transition(
                    source, phase
                )
                self.assertEqual((letter, valuation), ("B", 2))
                phase = 1 - phase

    def test_residual_three_two_frame_transfer(self) -> None:
        for b in range(1, 100000):
            if b % 64 not in {4, 25, 38, 59}:
                continue
            q = transformed_B(transformed_A(b))
            source = transformed_A(q)
            phase = source_A_selecting_tail_bit(
                transformed_A(transformed_A(b))
            )
            coefficient = embedded_original_state(source)
            upper = constant_tail_state(coefficient, 3, phase)
            lower = constant_tail_state(coefficient, 2, phase)
            factor_upper = constant_tail_state(3 * coefficient, 2, phase)
            factor_lower = constant_tail_state(3 * coefficient, 1, phase)
            side = transformed_B(lower)

            self.assertEqual(
                transformed_moves(upper),
                (factor_upper, factor_lower),
            )
            self.assertEqual(
                transformed_moves(lower),
                (factor_lower, side),
            )
            if phase == source_A_selecting_tail_bit(source):
                self.assertIn(side, transformed_moves(transformed_A(source)))
            else:
                self.assertEqual(
                    constant_tail_source_coordinates(side)[:2],
                    (transformed_B(source), 0),
                )

    def test_factor_frame_exits_within_two_levels(self) -> None:
        for b in range(1, 100000):
            if b % 64 not in {4, 25, 38, 59}:
                continue
            q = transformed_B(transformed_A(b))
            source = transformed_A(q)
            phase = source_A_selecting_tail_bit(
                transformed_A(transformed_A(b))
            )
            base_coefficient = embedded_original_state(source)

            for factor_power in (1, 2):
                coefficient = (3**factor_power) * base_coefficient
                upper = constant_tail_state(coefficient, 2, phase)
                lower = constant_tail_state(coefficient, 1, phase)
                following_factor = constant_tail_state(
                    3 * coefficient, 1, phase
                )
                side = transformed_B(lower)
                signed = transformed_A(lower)

                self.assertEqual(
                    transformed_moves(upper),
                    (following_factor, side),
                )
                self.assertEqual(
                    transformed_moves(lower),
                    (signed, side),
                )
                returned_source, returned_power, exponent, tail = (
                    constant_tail_source_coordinates(signed)
                )
                self.assertEqual(returned_power, 0)
                self.assertEqual(tail, 1 - phase)
                if exponent >= 2:
                    self.assertEqual(
                        constant_tail_source_coordinates(side),
                        (
                            returned_source,
                            0,
                            exponent - 1,
                            1 - phase,
                        ),
                    )

    def test_arbitrary_factor_frame_two_level_exit_geometry(self) -> None:
        for base_coefficient in range(1, 200, 2):
            for phase in (0, 1):
                for factor_exponent in range(7):
                    coefficient = (
                        3**factor_exponent * base_coefficient
                    )
                    upper = constant_tail_state(
                        coefficient, 2, phase
                    )
                    lower = constant_tail_state(
                        coefficient, 1, phase
                    )
                    next_lower = constant_tail_state(
                        3 * coefficient, 1, phase
                    )
                    current_side = transformed_B(lower)
                    current_signed = transformed_A(lower)
                    next_side = transformed_B(next_lower)
                    next_signed = transformed_A(next_lower)

                    self.assertEqual(
                        transformed_moves(upper),
                        (next_lower, current_side),
                    )
                    self.assertEqual(
                        transformed_moves(lower),
                        (current_signed, current_side),
                    )
                    self.assertEqual(
                        transformed_moves(next_lower),
                        (next_signed, next_side),
                    )

    def test_factor_frame_has_exact_reverse_parent(self) -> None:
        for base_coefficient in range(1, 200, 2):
            if base_coefficient % 3 == 0:
                continue
            for phase in (0, 1):
                for factor_exponent in range(1, 8):
                    preceding_coefficient = (
                        3 ** (factor_exponent - 1)
                        * base_coefficient
                    )
                    upper = constant_tail_state(
                        3 * preceding_coefficient,
                        2,
                        phase,
                    )
                    lower = constant_tail_state(
                        3 * preceding_coefficient,
                        1,
                        phase,
                    )
                    reverse_parent = constant_tail_state(
                        preceding_coefficient,
                        3,
                        phase,
                    )
                    self.assertEqual(
                        transformed_moves(reverse_parent),
                        (upper, lower),
                    )

                    if factor_exponent >= 2:
                        preceding_upper = constant_tail_state(
                            preceding_coefficient,
                            2,
                            phase,
                        )
                        boundary_parent = constant_tail_state(
                            3 ** (factor_exponent - 2)
                            * base_coefficient,
                            4,
                            phase,
                        )
                        self.assertEqual(
                            transformed_moves(boundary_parent),
                            (reverse_parent, preceding_upper),
                        )

    def test_valuation_three_frame_has_first_boundary_parent(self) -> None:
        for source in range(1, 10000):
            for input_phase in (0, 1):
                _, valuation, returned_source = source_boundary_transition(
                    source,
                    input_phase,
                )
                if valuation != 3:
                    continue

                phase = 1 - input_phase
                coefficient = embedded_original_state(returned_source)
                upper = constant_tail_state(coefficient, 3, phase)
                lower = constant_tail_state(coefficient, 2, phase)
                boundary_parent = (2 * upper + phase - 1) // 3

                self.assertEqual(coefficient % 3, 1 + phase)
                self.assertEqual(
                    transformed_moves(boundary_parent),
                    (upper, lower),
                )

    def test_ninefold_twenty_sevenfold_source_coupling(self) -> None:
        for b in range(1, 100000):
            if b % 64 not in {4, 25, 38, 59}:
                continue
            q = transformed_B(transformed_A(b))
            source = transformed_A(q)
            phase = source_A_selecting_tail_bit(
                transformed_A(transformed_A(b))
            )
            base_coefficient = embedded_original_state(source)

            first = transformed_A(
                constant_tail_state(3 * base_coefficient, 1, phase)
            )
            first_source, first_power, valuation, _ = (
                constant_tail_source_coordinates(first)
            )
            self.assertEqual(first_power, 0)

            second = transformed_A(
                constant_tail_state(9 * base_coefficient, 1, phase)
            )
            second_source, second_power, second_valuation, _ = (
                constant_tail_source_coordinates(second)
            )
            self.assertEqual(second_power, 0)

            if valuation >= 2:
                self.assertEqual(second_valuation, 1)
                self.assertEqual(
                    second_source,
                    constant_tail_state(
                        embedded_original_state(first_source),
                        valuation - 1,
                        1 - phase,
                    ),
                )
            else:
                self.assertEqual(
                    constant_tail_source_coordinates(first_source)[:2],
                    (transformed_B(source), 0),
                )
                _, selected_valuation, selected_source = (
                    source_boundary_transition(first_source, 1 - phase)
                )
                self.assertEqual(second_valuation, selected_valuation + 1)
                self.assertEqual(second_source, selected_source)

    def test_all_consecutive_factor_levels_are_coupled(self) -> None:
        for source in range(100):
            base_coefficient = embedded_original_state(source)
            for phase in (0, 1):
                for factor_exponent in range(9):
                    current_value = (
                        3 ** (factor_exponent + 1) * base_coefficient
                        + 1
                        - 2 * phase
                    )
                    current_valuation = v2(current_value)
                    current_coefficient = (
                        current_value >> current_valuation
                    )
                    current_source, current_power = (
                        constant_tail_coefficient_source(
                            current_coefficient
                        )
                    )
                    self.assertEqual(current_power, 0)

                    next_value = (
                        3 ** (factor_exponent + 2) * base_coefficient
                        + 1
                        - 2 * phase
                    )
                    next_valuation = v2(next_value)
                    next_coefficient = next_value >> next_valuation
                    next_source, next_power = (
                        constant_tail_coefficient_source(next_coefficient)
                    )
                    self.assertEqual(next_power, 0)

                    if current_valuation >= 2:
                        self.assertEqual(next_valuation, 1)
                        self.assertEqual(
                            next_source,
                            constant_tail_state(
                                embedded_original_state(current_source),
                                current_valuation - 1,
                                1 - phase,
                            ),
                        )
                    else:
                        if current_source == 0:
                            selected_value = 2 + 2 * phase
                            self.assertEqual(
                                next_valuation,
                                v2(selected_value) + 1,
                            )
                            self.assertEqual(next_source, 0)
                            continue
                        (
                            _,
                            selected_valuation,
                            selected_source,
                        ) = source_boundary_transition(
                            current_source, 1 - phase
                        )
                        self.assertEqual(
                            next_valuation, selected_valuation + 1
                        )
                        self.assertEqual(
                            next_source, selected_source
                        )

    def test_high_valuation_successor_raw_return(self) -> None:
        for source in range(1000):
            coefficient = embedded_original_state(source)
            for phase in (0, 1):
                return_phase = 1 - phase
                for valuation in range(2, 11):
                    successor_source = constant_tail_state(
                        coefficient,
                        valuation - 1,
                        return_phase,
                    )
                    successor_signed = constant_tail_state(
                        embedded_original_state(successor_source),
                        1,
                        return_phase,
                    )
                    successor_raw = alternating_suffix_remainder(
                        successor_signed
                    )

                    if valuation == 2:
                        self.assertEqual(
                            successor_raw,
                            transformed_A(successor_source),
                        )
                        self.assertEqual(
                            successor_raw,
                            constant_tail_state(
                                3 * coefficient,
                                0,
                                return_phase,
                            ),
                        )
                        if source > 0:
                            (
                                _,
                                selected_valuation,
                                selected_source,
                            ) = source_boundary_transition(
                                source,
                                return_phase,
                            )
                            self.assertEqual(
                                constant_tail_source_coordinates(
                                    successor_raw
                                ),
                                (
                                    selected_source,
                                    0,
                                    selected_valuation,
                                    1 - return_phase,
                                ),
                            )
                    else:
                        self.assertEqual(
                            successor_raw,
                            transformed_B(successor_source),
                        )
                        self.assertNotEqual(
                            return_phase,
                            source_A_selecting_tail_bit(
                                successor_source
                            ),
                        )

                    if valuation == 3:
                        self.assertEqual(
                            successor_raw,
                            alternating_suffix_remainder(
                                constant_tail_state(
                                    3 * coefficient,
                                    1,
                                    return_phase,
                                )
                            ),
                        )
                        if source > 0:
                            raw_source = (
                                0
                                if successor_raw == 0
                                else constant_tail_source_coordinates(
                                    successor_raw
                                )[0]
                            )
                            self.assertLess(raw_source, source)

                    if valuation >= 4:
                        self.assertEqual(
                            constant_tail_source_coordinates(
                                successor_raw
                            ),
                            (
                                source,
                                1,
                                valuation - 3,
                                return_phase,
                            ),
                        )

                    if valuation >= 5:
                        upper_reverse = constant_tail_state(
                            coefficient,
                            valuation - 1,
                            return_phase,
                        )
                        lower_reverse = constant_tail_state(
                            coefficient,
                            valuation - 2,
                            return_phase,
                        )
                        self.assertIn(
                            successor_raw,
                            transformed_moves(upper_reverse),
                        )
                        self.assertIn(
                            successor_raw,
                            transformed_moves(lower_reverse),
                        )
                        self.assertEqual(
                            source_boundary_transition(
                                successor_source,
                                return_phase,
                            ),
                            ("B", 2, successor_raw),
                        )
                        self.assertEqual(
                            source_A_selecting_tail_bit(successor_raw),
                            phase,
                        )

    def test_high_return_source_exception_filter(self) -> None:
        for source in range(1000):
            coefficient = embedded_original_state(source)
            selected = transformed_A(source)
            for phase in (0, 1):
                exponent_two = constant_tail_state(
                    3 * coefficient,
                    2,
                    phase,
                )
                is_exceptional = (
                    exponent_two % 16
                    in SIDE_RELATION_EXCEPTIONAL_RESIDUES
                )
                self.assertEqual(
                    is_exceptional,
                    selected % 2 == phase,
                )
                if is_exceptional:
                    core = 9 * selected + 4
                    self.assertEqual(
                        transformed_B(exponent_two),
                        alternating_suffix_remainder(core),
                    )
                    self.assertEqual(
                        transformed_B(transformed_A(exponent_two)),
                        3 * core + 1,
                    )

                for valuation in range(6, 11):
                    high_return = constant_tail_state(
                        3 * coefficient,
                        valuation - 3,
                        phase,
                    )
                    self.assertNotIn(
                        high_return % 16,
                        SIDE_RELATION_EXCEPTIONAL_RESIDUES,
                    )

    def test_exponent_one_lift_B_child_source_decreases(self) -> None:
        for source in range(1, 100000):
            coefficient = embedded_original_state(source)
            for phase in (0, 1):
                lifted = constant_tail_state(coefficient, 1, phase)
                selected = transformed_B(lifted)
                if selected == 0:
                    continue
                selected_source = constant_tail_source_coordinates(
                    selected
                )[0]
                self.assertLess(selected_source, source)

    def test_long_tail_common_token_chain_coordinates(self) -> None:
        for coefficient in range(1, 1000, 2):
            for phase in (0, 1):
                for initial_exponent in range(4, 25):
                    current_coefficient = coefficient
                    current_exponent = initial_exponent
                    current = constant_tail_state(
                        current_coefficient,
                        current_exponent,
                        phase,
                    )
                    while current_exponent >= 4:
                        side = transformed_B(current)
                        common = transformed_B(transformed_A(current))
                        self.assertEqual(
                            side,
                            constant_tail_state(
                                3 * current_coefficient,
                                current_exponent - 2,
                                phase,
                            ),
                        )
                        self.assertEqual(common, transformed_A(side))
                        self.assertEqual(
                            common,
                            constant_tail_state(
                                9 * current_coefficient,
                                current_exponent - 3,
                                phase,
                            ),
                        )
                        current = common
                        current_coefficient *= 9
                        current_exponent -= 3

    def test_stable_q4_q3_three_level_exit_sources(self) -> None:
        for source in range(1, 1000):
            source_coefficient = embedded_original_state(source)
            for phase in (0, 1):
                exit_phase = 1 - phase
                for valuation in range(20, 29):
                    token = constant_tail_state(
                        2187 * source_coefficient,
                        valuation - 12,
                        phase,
                    )
                    factor_source = transformed_B(token)
                    first_lower_token = transformed_B(
                        transformed_A(token)
                    )
                    marked_source = transformed_B(first_lower_token)
                    second_lower_token = transformed_B(
                        transformed_A(first_lower_token)
                    )
                    selected_sibling = transformed_B(marked_source)

                    self.assertEqual(
                        second_lower_token,
                        transformed_A(marked_source),
                    )
                    self.assertEqual(
                        source_boundary_transition(marked_source, phase),
                        ("B", 2, selected_sibling),
                    )

                    coefficient = embedded_original_state(factor_source)
                    first_numerator = (
                        9 * coefficient + 1 - 2 * exit_phase
                    )
                    self.assertEqual(
                        first_numerator,
                        8 * embedded_original_state(marked_source),
                    )
                    self.assertEqual(v2(first_numerator), 3)

                    first_raw = constant_tail_state(
                        embedded_original_state(marked_source),
                        2,
                        phase,
                    )
                    second_numerator = (
                        27 * coefficient + 1 - 2 * exit_phase
                    )
                    self.assertEqual(
                        second_numerator,
                        2 * embedded_original_state(first_raw),
                    )
                    self.assertEqual(v2(second_numerator), 1)

                    third_numerator = (
                        81 * coefficient + 1 - 2 * exit_phase
                    )
                    transition = source_boundary_transition(
                        first_raw,
                        phase,
                    )
                    self.assertEqual(transition[0], "B")
                    self.assertGreaterEqual(transition[1], 3)
                    self.assertEqual(
                        third_numerator,
                        (1 << (transition[1] + 1))
                        * embedded_original_state(transition[2]),
                    )
                    self.assertEqual(
                        constant_tail_source_coordinates(transition[2]),
                        (selected_sibling, 0, 1, exit_phase),
                    )

    def test_universal_marked_factor_macro_drops_eleven_tail_bits(
        self,
    ) -> None:
        for coefficient in range(1, 200, 2):
            for phase in (0, 1):
                for exponent in range(14, 26):
                    factor_source = constant_tail_state(
                        coefficient,
                        exponent,
                        phase,
                    )
                    marked_child = transformed_A(factor_source)
                    loss_child = transformed_B(factor_source)
                    first_common = transformed_B(marked_child)

                    first_numerator = (
                        9 * embedded_original_state(factor_source)
                        + 1
                        - 2 * phase
                    )
                    self.assertEqual(v2(first_numerator), 1)
                    first_lift_source = constant_tail_coefficient_source(
                        first_numerator >> 1
                    )[0]
                    first_signed = constant_tail_state(
                        embedded_original_state(first_lift_source),
                        1,
                        1 - phase,
                    )
                    first_raw = alternating_suffix_remainder(first_signed)
                    self.assertEqual(
                        first_raw,
                        constant_tail_state(
                            embedded_original_state(first_common),
                            1,
                            phase,
                        ),
                    )

                    nested_source = transformed_B(first_raw)
                    nested_transition = source_boundary_transition(
                        nested_source,
                        phase,
                    )
                    self.assertEqual(nested_transition[:2], ("B", 4))

                    lower_token = transformed_B(
                        transformed_A(first_common)
                    )
                    returned_source = nested_transition[2]
                    self.assertEqual(
                        lower_token,
                        constant_tail_state(
                            81 * coefficient,
                            exponent - 6,
                            phase,
                        ),
                    )
                    self.assertEqual(
                        returned_source,
                        constant_tail_state(
                            243 * coefficient,
                            exponent - 8,
                            phase,
                        ),
                    )
                    self.assertEqual(
                        returned_source,
                        transformed_B(lower_token),
                    )

                    intermediate_token = transformed_B(
                        transformed_A(lower_token)
                    )
                    following_source = transformed_B(intermediate_token)
                    following_marked = transformed_B(
                        transformed_A(intermediate_token)
                    )
                    following_loss = transformed_B(following_source)
                    self.assertEqual(
                        intermediate_token,
                        constant_tail_state(
                            729 * coefficient,
                            exponent - 9,
                            phase,
                        ),
                    )
                    self.assertEqual(
                        following_source,
                        constant_tail_state(
                            2187 * coefficient,
                            exponent - 11,
                            phase,
                        ),
                    )
                    self.assertEqual(
                        following_marked,
                        constant_tail_state(
                            6561 * coefficient,
                            exponent - 12,
                            phase,
                        ),
                    )
                    self.assertEqual(
                        following_loss,
                        constant_tail_state(
                            6561 * coefficient,
                            exponent - 13,
                            phase,
                        ),
                    )
                    self.assertEqual(
                        following_marked,
                        transformed_A(following_source),
                    )
                    self.assertEqual(
                        source_boundary_transition(
                            following_source,
                            phase,
                        ),
                        ("B", 2, following_loss),
                    )
                    self.assertEqual(
                        9 * embedded_original_state(returned_source)
                        + 1
                        - 2 * (1 - phase),
                        8 * embedded_original_state(following_source),
                    )

    def test_short_marked_row_enters_A_selecting_obligation(self) -> None:
        for coefficient in range(1, 1000, 2):
            for phase in (0, 1):
                factor_source = constant_tail_state(
                    coefficient,
                    3,
                    phase,
                )
                marked_child = transformed_A(factor_source)
                loss_child = transformed_B(factor_source)
                common_token = transformed_B(marked_child)
                self.assertEqual(
                    common_token,
                    transformed_B(loss_child),
                )

                first_numerator = (
                    9 * embedded_original_state(factor_source)
                    + 1
                    - 2 * phase
                )
                self.assertEqual(v2(first_numerator), 1)
                lifted_source = constant_tail_coefficient_source(
                    first_numerator >> 1
                )[0]
                first_signed = constant_tail_state(
                    embedded_original_state(lifted_source),
                    1,
                    1 - phase,
                )
                first_raw = alternating_suffix_remainder(first_signed)
                self.assertEqual(first_raw, transformed_A(lifted_source))
                raw_coordinates = constant_tail_source_coordinates(
                    first_raw
                )
                self.assertEqual(raw_coordinates[:2], (common_token, 0))
                self.assertGreaterEqual(raw_coordinates[2], 2)
                self.assertEqual(raw_coordinates[3], phase)
                self.assertEqual(
                    source_A_selecting_tail_bit(first_raw),
                    1 - phase,
                )

                second_numerator = (
                    27 * embedded_original_state(factor_source)
                    + 1
                    - 2 * phase
                )
                self.assertEqual(
                    second_numerator,
                    4 * embedded_original_state(first_raw),
                )
                self.assertEqual(v2(second_numerator), 2)

    def test_long_lift_A_obligation_canonical_recycle(self) -> None:
        for source in range(1, 1000):
            base_coefficient = embedded_original_state(source)
            for factor_power in range(0, 7, 2):
                coefficient = 3**factor_power * base_coefficient
                for phase in (0, 1):
                    selecting_phase = 1 - phase
                    for exponent in range(2, 13):
                        obligation_source = constant_tail_state(
                            coefficient,
                            exponent,
                            phase,
                        )
                        self.assertEqual(
                            source_A_selecting_tail_bit(
                                obligation_source
                            ),
                            selecting_phase,
                        )

                        selected_source = transformed_A(
                            obligation_source
                        )
                        lower = constant_tail_state(
                            embedded_original_state(obligation_source),
                            1,
                            selecting_phase,
                        )
                        upper = constant_tail_state(
                            embedded_original_state(obligation_source),
                            2,
                            selecting_phase,
                        )
                        common_side = transformed_B(lower)
                        self.assertEqual(
                            transformed_B(upper), common_side
                        )

                        transition = source_boundary_transition(
                            selected_source,
                            phase,
                        )
                        self.assertEqual(transition[2], common_side)

                        if exponent == 2:
                            self.assertEqual(transition[:2], ("A", 1))
                            self.assertEqual(
                                common_side,
                                transformed_A(selected_source),
                            )
                            self.assertEqual(
                                source_A_selecting_tail_bit(
                                    selected_source
                                ),
                                phase,
                            )
                        elif exponent == 3:
                            self.assertEqual(transition[0], "B")
                            self.assertGreaterEqual(transition[1], 3)
                            self.assertEqual(
                                common_side,
                                alternating_suffix_remainder(
                                    constant_tail_state(
                                        9 * coefficient,
                                        1,
                                        phase,
                                    )
                                ),
                            )
                            self.assertEqual(
                                source_A_selecting_tail_bit(
                                    selected_source
                                ),
                                selecting_phase,
                            )
                            self.assertNotIn(
                                obligation_source % 16,
                                SIDE_RELATION_EXCEPTIONAL_RESIDUES,
                            )
                            self.assertEqual(
                                common_side,
                                transformed_B(selected_source),
                            )
                            self.assertIn(
                                common_side,
                                transformed_moves(
                                    transformed_B(obligation_source)
                                ),
                            )
                        else:
                            self.assertEqual(transition[:2], ("B", 2))
                            self.assertEqual(
                                common_side,
                                constant_tail_state(
                                    9 * coefficient,
                                    exponent - 3,
                                    phase,
                                ),
                            )
                            self.assertEqual(
                                constant_tail_source_coordinates(
                                    common_side
                                ),
                                (
                                    source,
                                    factor_power + 2,
                                    exponent - 3,
                                    phase,
                                ),
                            )
                            self.assertEqual(
                                source_A_selecting_tail_bit(
                                    selected_source
                                ),
                                selecting_phase,
                            )
                            self.assertNotIn(
                                obligation_source % 16,
                                SIDE_RELATION_EXCEPTIONAL_RESIDUES,
                            )
                            self.assertEqual(
                                common_side,
                                transformed_B(selected_source),
                            )
                            self.assertIn(
                                common_side,
                                transformed_moves(
                                    transformed_B(obligation_source)
                                ),
                            )

    def test_high_return_obligation_common_side(self) -> None:
        for source in range(1, 1000):
            coefficient = embedded_original_state(source)
            for phase in (0, 1):
                for valuation in range(5, 21):
                    returned_token = constant_tail_state(
                        3 * coefficient,
                        valuation - 3,
                        phase,
                    )
                    selecting_phase = source_A_selecting_tail_bit(
                        returned_token
                    )
                    self.assertEqual(selecting_phase, 1 - phase)

                    lower = constant_tail_state(
                        embedded_original_state(returned_token),
                        1,
                        selecting_phase,
                    )
                    upper = constant_tail_state(
                        embedded_original_state(returned_token),
                        2,
                        selecting_phase,
                    )
                    common_side = transformed_B(lower)
                    self.assertEqual(
                        transformed_B(upper),
                        common_side,
                    )

                    selected_source = transformed_A(returned_token)
                    self.assertEqual(
                        selected_source,
                        constant_tail_state(
                            9 * coefficient,
                            valuation - 4,
                            phase,
                        ),
                    )

                    if valuation == 5:
                        self.assertEqual(
                            common_side,
                            transformed_A(selected_source),
                        )
                        self.assertEqual(
                            common_side,
                            27 * coefficient - phase,
                        )
                    else:
                        self.assertEqual(
                            common_side,
                            transformed_B(selected_source),
                        )
                        if valuation == 6:
                            self.assertEqual(
                                common_side,
                                alternating_suffix_remainder(
                                    constant_tail_state(
                                        27 * coefficient,
                                        1,
                                        phase,
                                    )
                                ),
                            )
                        else:
                            self.assertEqual(
                                constant_tail_source_coordinates(
                                    common_side
                                ),
                                (
                                    source,
                                    3,
                                    valuation - 6,
                                    phase,
                                ),
                            )

    def test_high_return_predecessor_token_diamond(self) -> None:
        for source in range(1, 10000):
            coefficient = embedded_original_state(source)
            for phase in (0, 1):
                for valuation in range(5, 21):
                    predecessor_token = constant_tail_state(
                        coefficient,
                        valuation - 1,
                        phase,
                    )
                    returned_source = transformed_B(predecessor_token)
                    self.assertEqual(
                        returned_source,
                        constant_tail_state(
                            3 * coefficient,
                            valuation - 3,
                            phase,
                        ),
                    )
                    self.assertNotIn(
                        predecessor_token % 16,
                        SIDE_RELATION_EXCEPTIONAL_RESIDUES,
                    )

                    lower_win = transformed_B(
                        transformed_A(predecessor_token)
                    )
                    self.assertEqual(
                        lower_win,
                        transformed_A(returned_source),
                    )
                    self.assertIn(
                        lower_win,
                        transformed_moves(returned_source),
                    )

                    selecting_phase = source_A_selecting_tail_bit(
                        returned_source
                    )
                    obligation_lower = constant_tail_state(
                        embedded_original_state(returned_source),
                        1,
                        selecting_phase,
                    )
                    common_side = transformed_B(obligation_lower)
                    self.assertIn(
                        common_side,
                        transformed_moves(lower_win),
                    )
                    if valuation == 5:
                        self.assertEqual(
                            common_side,
                            transformed_A(lower_win),
                        )
                    else:
                        self.assertEqual(
                            common_side,
                            transformed_B(lower_win),
                        )

                    if valuation == 5:
                        exceptional_residues = {1, 14}
                    elif valuation == 6:
                        exceptional_residues = {3, 12}
                    else:
                        exceptional_residues = set()
                    if (
                        lower_win % 16
                        in SIDE_RELATION_EXCEPTIONAL_RESIDUES
                    ):
                        self.assertIn(
                            lower_win % 16,
                            exceptional_residues,
                        )
                    elif exceptional_residues:
                        self.assertNotIn(
                            lower_win % 16,
                            SIDE_RELATION_EXCEPTIONAL_RESIDUES,
                        )

                    if (
                        lower_win % 16
                        not in SIDE_RELATION_EXCEPTIONAL_RESIDUES
                    ):
                        common_descendant = transformed_B(
                            transformed_A(lower_win)
                        )
                        for child in transformed_moves(lower_win):
                            self.assertIn(
                                common_descendant,
                                transformed_moves(child),
                            )

                    predecessor_transition = source_boundary_transition(
                        lower_win,
                        phase,
                    )
                    self.assertEqual(
                        predecessor_transition[2],
                        common_side,
                    )
                    if valuation == 5:
                        self.assertEqual(
                            predecessor_transition[:2],
                            ("A", 1),
                        )
                    elif valuation == 6:
                        self.assertEqual(
                            predecessor_transition[0],
                            "B",
                        )
                        self.assertGreaterEqual(
                            predecessor_transition[1],
                            3,
                        )
                    else:
                        self.assertEqual(
                            predecessor_transition[:2],
                            ("B", 2),
                        )

                    if valuation < 7:
                        continue

                    lower_child = transformed_B(
                        transformed_A(lower_win)
                    )
                    other_factor_child = next(
                        child
                        for child in transformed_moves(common_side)
                        if child != lower_child
                    )
                    factor_transition = source_boundary_transition(
                        common_side,
                        phase,
                    )
                    self.assertEqual(
                        factor_transition[2],
                        other_factor_child,
                    )
                    if valuation == 7:
                        self.assertEqual(
                            lower_child,
                            transformed_B(common_side),
                        )
                        self.assertEqual(
                            factor_transition[:2],
                            ("A", 1),
                        )
                    else:
                        self.assertEqual(
                            lower_child,
                            transformed_A(common_side),
                        )
                        self.assertEqual(
                            factor_transition[0],
                            "B",
                        )
                        if valuation == 8:
                            self.assertGreaterEqual(
                                factor_transition[1],
                                3,
                            )
                        else:
                            self.assertEqual(
                                factor_transition[1],
                                2,
                            )

                    if valuation < 9:
                        continue

                    common_token = transformed_B(lower_child)
                    self.assertIn(
                        common_token,
                        transformed_moves(other_factor_child),
                    )
                    first_factor_numerator = (
                        9 * embedded_original_state(common_side)
                        + 1
                        - 2 * phase
                    )
                    first_factor_valuation = v2(
                        first_factor_numerator
                    )
                    self.assertEqual(first_factor_valuation, 1)
                    first_factor_coefficient = (
                        first_factor_numerator
                        >> first_factor_valuation
                    )
                    first_factor_source = inverse_F(
                        (first_factor_coefficient - 1) // 2
                    )
                    self.assertEqual(
                        first_factor_source,
                        constant_tail_state(
                            embedded_original_state(other_factor_child),
                            1,
                            1 - phase,
                        ),
                    )
                    first_signed_exit = constant_tail_state(
                        embedded_original_state(first_factor_source),
                        first_factor_valuation,
                        1 - phase,
                    )
                    first_raw_exit = alternating_suffix_remainder(
                        first_signed_exit
                    )
                    raw_coordinates = constant_tail_source_coordinates(
                        first_raw_exit
                    )
                    self.assertEqual(raw_coordinates[0], common_token)
                    self.assertEqual(raw_coordinates[1], 0)
                    self.assertEqual(raw_coordinates[3], phase)
                    if valuation == 9:
                        self.assertGreaterEqual(raw_coordinates[2], 2)
                    else:
                        self.assertEqual(raw_coordinates[2], 1)

                    self.assertEqual(
                        source_A_selecting_tail_bit(first_factor_source),
                        1 - phase,
                    )
                    self.assertEqual(
                        transformed_A(first_factor_source),
                        first_raw_exit,
                    )
                    self.assertEqual(
                        transformed_A(first_signed_exit),
                        constant_tail_state(
                            embedded_original_state(first_raw_exit),
                            1,
                            phase,
                        ),
                    )

                    if valuation < 10:
                        continue

                    following_token = transformed_B(first_factor_source)
                    self.assertIn(
                        following_token,
                        transformed_moves(common_token),
                    )
                    common_transition = source_boundary_transition(
                        common_token,
                        phase,
                    )
                    self.assertEqual(
                        common_transition[2],
                        following_token,
                    )
                    if valuation == 10:
                        self.assertEqual(common_transition[:2], ("A", 1))
                    elif valuation == 11:
                        self.assertEqual(common_transition[0], "B")
                        self.assertGreaterEqual(common_transition[1], 3)
                    else:
                        self.assertEqual(common_transition[:2], ("B", 2))

                    nested_common_side = transformed_B(
                        first_signed_exit
                    )
                    self.assertEqual(
                        nested_common_side,
                        constant_tail_state(
                            embedded_original_state(following_token),
                            common_transition[1],
                            1 - phase,
                        ),
                    )

                    second_factor_numerator = (
                        27 * embedded_original_state(common_side)
                        + 1
                        - 2 * phase
                    )
                    self.assertEqual(v2(second_factor_numerator), 2)
                    second_factor_source = inverse_F(
                        ((second_factor_numerator >> 2) - 1) // 2
                    )
                    self.assertEqual(
                        second_factor_source,
                        first_raw_exit,
                    )

                    second_signed_exit = constant_tail_state(
                        embedded_original_state(first_raw_exit),
                        2,
                        1 - phase,
                    )
                    second_raw_exit = alternating_suffix_remainder(
                        second_signed_exit
                    )
                    self.assertEqual(
                        second_raw_exit,
                        constant_tail_state(
                            embedded_original_state(first_raw_exit),
                            1,
                            1 - phase,
                        ),
                    )

                    second_transition = source_boundary_transition(
                        first_raw_exit,
                        1 - phase,
                    )
                    self.assertEqual(second_transition[0], "B")
                    if valuation == 10:
                        self.assertGreaterEqual(second_transition[1], 3)
                    else:
                        self.assertEqual(second_transition[1], 2)
                    self.assertEqual(
                        second_transition[2],
                        transformed_B(first_raw_exit),
                    )

                    transfer_source = second_transition[2]
                    transfer_valuation = second_transition[1]
                    transfer_common_side = transformed_B(second_raw_exit)
                    self.assertEqual(
                        transfer_common_side,
                        transformed_B(second_signed_exit),
                    )
                    self.assertEqual(
                        transformed_A(second_raw_exit),
                        constant_tail_state(
                            embedded_original_state(transfer_source),
                            transfer_valuation,
                            phase,
                        ),
                    )
                    self.assertEqual(
                        transfer_common_side,
                        constant_tail_state(
                            embedded_original_state(transfer_source),
                            transfer_valuation - 1,
                            phase,
                        ),
                    )

                    if valuation >= 11:
                        self.assertEqual(common_transition[0], "B")
                        self.assertEqual(
                            transfer_source,
                            constant_tail_state(
                                embedded_original_state(following_token),
                                common_transition[1] - 1,
                                1 - phase,
                            ),
                        )
                        expected_selecting_phase = (
                            phase if valuation == 11 else 1 - phase
                        )
                        self.assertEqual(
                            source_A_selecting_tail_bit(transfer_source),
                            expected_selecting_phase,
                        )

                    if valuation >= 12:
                        lower_common_token = transformed_B(
                            transformed_A(common_token)
                        )
                        if valuation == 12:
                            self.assertEqual(
                                lower_common_token,
                                transformed_B(following_token),
                            )
                        else:
                            self.assertEqual(
                                lower_common_token,
                                transformed_A(following_token),
                            )

                        nested_transition = source_boundary_transition(
                            transfer_source,
                            phase,
                        )
                        self.assertEqual(nested_transition[0], "B")
                        if valuation == 12:
                            self.assertEqual(nested_transition[1], 2)
                        elif valuation == 13:
                            self.assertEqual(nested_transition[1], 3)
                        elif valuation == 14:
                            self.assertGreaterEqual(
                                nested_transition[1],
                                5,
                            )
                        else:
                            self.assertEqual(nested_transition[1], 4)

                        nested_source = nested_transition[2]
                        if valuation == 12:
                            self.assertEqual(
                                constant_tail_source_coordinates(
                                    nested_source
                                )[:2],
                                (lower_common_token, 0),
                            )
                        elif valuation == 13:
                            self.assertEqual(
                                nested_source,
                                transformed_A(lower_common_token),
                            )
                        else:
                            self.assertEqual(
                                nested_source,
                                transformed_B(lower_common_token),
                            )

    def test_short_high_return_token_diamonds(self) -> None:
        for source in range(1, 10000):
            coefficient = embedded_original_state(source)
            for phase in (0, 1):
                for valuation in (5, 6):
                    returned_token = constant_tail_state(
                        3 * coefficient,
                        valuation - 3,
                        phase,
                    )
                    selecting_phase = source_A_selecting_tail_bit(
                        returned_token
                    )
                    lower = constant_tail_state(
                        embedded_original_state(returned_token),
                        1,
                        selecting_phase,
                    )
                    common_side = transformed_B(lower)
                    selected_source = transformed_A(returned_token)
                    opposite_child = transformed_B(selected_source)

                    if valuation == 5:
                        self.assertEqual(
                            common_side,
                            transformed_A(selected_source),
                        )
                        if (
                            returned_token % 16
                            in SIDE_RELATION_EXCEPTIONAL_RESIDUES
                        ):
                            loss_source = transformed_B(returned_token)
                            common_coordinates = (
                                constant_tail_source_coordinates(common_side)
                            )
                            opposite_coordinates = (
                                constant_tail_source_coordinates(
                                    opposite_child
                                )
                            )
                            self.assertEqual(
                                common_coordinates[:2],
                                (loss_source, 0),
                            )
                            self.assertEqual(
                                opposite_coordinates[:2],
                                (loss_source, 0),
                            )
                            self.assertEqual(
                                abs(
                                    common_coordinates[2]
                                    - opposite_coordinates[2]
                                ),
                                1,
                            )
                            self.assertEqual(
                                common_coordinates[3],
                                opposite_coordinates[3],
                            )
                        else:
                            self.assertIn(
                                opposite_child,
                                transformed_moves(
                                    transformed_B(returned_token)
                                ),
                            )
                    else:
                        self.assertNotIn(
                            returned_token % 16,
                            SIDE_RELATION_EXCEPTIONAL_RESIDUES,
                        )
                        self.assertEqual(common_side, opposite_child)
                        self.assertIn(
                            common_side,
                            transformed_moves(
                                transformed_B(returned_token)
                            ),
                        )

    def test_valuation_one_raw_exit_strict_source_drop(self) -> None:
        for source in range(1, 10000):
            coefficient = embedded_original_state(source)
            for phase in (0, 1):
                signed_state = constant_tail_state(
                    coefficient, 1, phase
                )
                raw_exit = alternating_suffix_remainder(signed_state)
                if raw_exit == 0:
                    continue
                raw_source = constant_tail_source_coordinates(
                    raw_exit
                )[0]
                self.assertLess(raw_source, source)

    def test_win_factor_source_return_provenance(self) -> None:
        for b in range(1, 100000):
            if b % 64 not in {4, 25, 38, 59}:
                continue
            q = transformed_B(transformed_A(b))
            source = transformed_A(q)
            phase = source_A_selecting_tail_bit(
                transformed_A(transformed_A(b))
            )
            coefficient = embedded_original_state(source)
            signed = transformed_A(
                constant_tail_state(3 * coefficient, 1, phase)
            )
            returned, returned_power, valuation, _ = (
                constant_tail_source_coordinates(signed)
            )
            self.assertEqual(returned_power, 0)
            token = transformed_B(source)

            if valuation == 1:
                self.assertEqual(
                    constant_tail_source_coordinates(returned)[:2],
                    (token, 0),
                )
            elif valuation >= 3:
                if source % 16 in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
                    self.assertEqual(
                        constant_tail_source_coordinates(returned)[:2],
                        (token, 0),
                    )
                else:
                    self.assertIn(returned, transformed_moves(token))

    def test_exceptional_token_valuation_two_strict_return(self) -> None:
        observed = set()
        for source in range(1, 100000):
            if source % 16 in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
                continue
            token = transformed_B(source)
            if token % 16 not in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
                continue
            coefficient = embedded_original_state(source)

            for phase in (0, 1):
                signed = transformed_A(
                    constant_tail_state(3 * coefficient, 1, phase)
                )
                _, _, valuation, _ = constant_tail_source_coordinates(signed)
                if valuation != 2:
                    continue

                returned = transformed_B(transformed_A(source))
                relation = (
                    "A"
                    if returned == transformed_A(token)
                    else "B"
                    if returned == transformed_B(token)
                    else None
                )
                observed.add((source % 256, phase, token % 16, relation))
                self.assertEqual(
                    alternating_suffix_length(transformed_A(source)),
                    2,
                )
                self.assertEqual(
                    relation,
                    "A" if token % 16 in {1, 14} else "B",
                )
                self.assertLess(transformed_A(returned), source)

        self.assertEqual(
            observed,
            {
                (4, 1, 1, "A"),
                (9, 1, 3, "B"),
                (38, 0, 14, "A"),
                (52, 1, 3, "B"),
                (75, 0, 12, "B"),
                (89, 1, 1, "A"),
                (118, 0, 12, "B"),
                (123, 0, 14, "A"),
                (132, 1, 1, "A"),
                (137, 1, 3, "B"),
                (166, 0, 14, "A"),
                (180, 1, 3, "B"),
                (203, 0, 12, "B"),
                (217, 1, 1, "A"),
                (246, 0, 12, "B"),
                (251, 0, 14, "A"),
            },
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

    def test_long_alternating_suffix_avoids_spine_exceptions(self) -> None:
        for state in range(1, 100000):
            if alternating_suffix_length(state) < 5:
                continue
            self.assertIn(state % 16, {5, 10})
            self.assertIn(transformed_A(state) % 16, {0, 15})

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

    def test_adjacent_tail_frame_has_one_common_child(self) -> None:
        for odd_coefficient in range(1, 200, 2):
            for tail_bit in (0, 1):
                for lower_exponent in range(1, 12):
                    lower = constant_tail_state(
                        odd_coefficient, lower_exponent, tail_bit
                    )
                    upper = constant_tail_state(
                        odd_coefficient, lower_exponent + 1, tail_bit
                    )
                    common = set(transformed_moves(lower)) & set(
                        transformed_moves(upper)
                    )
                    self.assertEqual(len(common), 1)

                    if lower_exponent >= 2:
                        self.assertEqual(
                            common,
                            {
                                constant_tail_state(
                                    3 * odd_coefficient,
                                    lower_exponent - 1,
                                    tail_bit,
                                )
                            },
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

    def test_three_z_plus_one_has_alternating_remainder_source(self) -> None:
        for z in range(100000):
            source, power, _, tail = constant_tail_source_coordinates(
                3 * z + 1
            )
            self.assertEqual(source, alternating_suffix_remainder(z))
            self.assertEqual(power, 0)
            self.assertEqual(tail, 1 - (z & 1))

    def test_factor_coefficient_second_source_trichotomy(self) -> None:
        for source in range(1, 100000):
            coefficient = 3 * embedded_original_state(source)
            for phase in (0, 1):
                lifted = constant_tail_state(coefficient, 1, phase)
                returned_source, power, valuation, _ = (
                    constant_tail_source_coordinates(transformed_A(lifted))
                )
                self.assertEqual(power, 0)

                if valuation == 1:
                    returned_state = 3 * transformed_A(source) + 1
                    self.assertEqual(returned_source, returned_state)
                    self.assertEqual(
                        constant_tail_source_coordinates(returned_state)[:2],
                        (transformed_B(source), 0),
                    )
                elif valuation == 2:
                    self.assertEqual(
                        returned_source,
                        transformed_A(transformed_A(source)),
                    )
                    returned_phase = 1 - phase
                    self.assertEqual(
                        returned_phase
                        == source_A_selecting_tail_bit(returned_source),
                        source % 16
                        in SIDE_RELATION_EXCEPTIONAL_RESIDUES,
                    )
                    if (
                        source % 16
                        not in SIDE_RELATION_EXCEPTIONAL_RESIDUES
                    ):
                        next_letter, next_valuation, next_source = (
                            source_boundary_transition(
                                returned_source,
                                returned_phase,
                            )
                        )
                        self.assertEqual(next_letter, "B")
                        middle = transformed_A(source)
                        lower_return = transformed_B(middle)
                        if (
                            middle % 16
                            in SIDE_RELATION_EXCEPTIONAL_RESIDUES
                        ):
                            self.assertEqual(next_valuation, 2)
                            self.assertEqual(
                                constant_tail_source_coordinates(
                                    next_source
                                )[:2],
                                (lower_return, 0),
                            )
                        else:
                            self.assertGreaterEqual(next_valuation, 3)
                            self.assertIn(
                                next_source,
                                transformed_moves(lower_return),
                            )
                            if next_valuation == 3:
                                self.assertEqual(
                                    next_source,
                                    transformed_A(lower_return),
                                )
                else:
                    self.assertEqual(
                        returned_source,
                        transformed_B(transformed_A(source)),
                    )

    def test_lifted_source_side_diamond(self) -> None:
        for odd_value in range(1, 10000, 2):
            coefficient = constant_tail_coordinates(3 * odd_value)[0]
            self.assertEqual(
                coefficient,
                embedded_original_state(
                    alternating_suffix_remainder(odd_value)
                ),
            )

            coefficient = constant_tail_coordinates(3 * odd_value - 1)[0]
            self.assertEqual(
                coefficient,
                embedded_original_state(
                    alternating_suffix_remainder(2 * odd_value - 1)
                ),
            )

        for source in range(1, 100000):
            phase = source_A_selecting_tail_bit(source)
            first_lift = constant_tail_state(
                embedded_original_state(source), 1, phase
            )
            second_lift = transformed_A(first_lift)
            self.assertEqual(
                second_lift,
                constant_tail_state(
                    embedded_original_state(transformed_A(source)),
                    1,
                    1 - phase,
                ),
            )

            lifted_side = transformed_B(second_lift)
            if lifted_side == 0:
                self.assertIn(source % 16, SIDE_RELATION_EXCEPTIONAL_RESIDUES)
                continue
            side_source, power_of_three, _, _ = (
                constant_tail_source_coordinates(lifted_side)
            )
            if source % 16 in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
                self.assertLess(side_source, source)
            else:
                self.assertEqual(power_of_three, 0)
                self.assertEqual(
                    side_source, transformed_B(transformed_A(source))
                )

    def test_nondecreasing_lifted_source_return(self) -> None:
        nondecreasing_residues = {0, 5, 10, 15}
        matching_phase_residues = {0, 10, 21, 31}

        for source in range(1, 100000):
            returned_source = transformed_B(transformed_A(source))
            if source % 16 not in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
                self.assertEqual(
                    returned_source >= source,
                    source % 16 in nondecreasing_residues,
                )

            if source % 16 not in nondecreasing_residues:
                continue

            phase = source_A_selecting_tail_bit(source)
            first = constant_tail_state(
                embedded_original_state(source), 1, phase
            )
            second = transformed_A(first)
            lower = transformed_B(second)
            upper = transformed_A(second)
            self.assertEqual(
                constant_tail_source_coordinates(lower),
                (returned_source, 0, 1, phase),
            )
            self.assertEqual(
                constant_tail_source_coordinates(upper),
                (returned_source, 0, 2, phase),
            )

            phases_match = phase == source_A_selecting_tail_bit(returned_source)
            self.assertEqual(
                phases_match,
                source % 32 in matching_phase_residues,
            )
            if phases_match:
                continue

            smaller_source = transformed_B(returned_source)
            self.assertLess(smaller_source, source)
            self.assertEqual(
                constant_tail_source_coordinates(transformed_A(lower))[0],
                smaller_source,
            )
            self.assertEqual(
                constant_tail_source_coordinates(transformed_B(lower))[0],
                smaller_source,
            )

            factor_three_state = transformed_A(upper)
            self.assertEqual(
                constant_tail_source_coordinates(factor_three_state),
                (returned_source, 1, 1, phase),
            )
            next_source = 3 * transformed_A(returned_source) + 1
            self.assertEqual(
                constant_tail_source_coordinates(
                    transformed_A(factor_three_state)
                ),
                (next_source, 0, 1, 1 - phase),
            )

    def test_phase_mismatch_large_diamond(self) -> None:
        for source in range(1, 100000):
            if source % 32 not in {5, 15, 16, 26}:
                continue

            returned_source = transformed_B(transformed_A(source))
            phase = source_A_selecting_tail_bit(source)
            lower = constant_tail_state(
                embedded_original_state(returned_source), 1, phase
            )
            upper = constant_tail_state(
                embedded_original_state(returned_source), 2, phase
            )
            lower_expanding = transformed_A(lower)
            lower_contracting = transformed_B(lower)
            factor_three_state = transformed_A(upper)

            common_children = set(transformed_moves(lower_expanding)) & set(
                transformed_moves(lower_contracting)
            )
            self.assertEqual(len(common_children), 1)
            other_child = next(
                child
                for child in transformed_moves(lower_contracting)
                if child not in common_children
            )
            self.assertEqual(transformed_B(factor_three_state), other_child)

    def test_phase_match_long_suffix_filter(self) -> None:
        long_suffix_residues = {21, 63, 64, 106}
        for source in range(1, 100000):
            if source % 32 not in {0, 10, 21, 31}:
                continue

            returned_source = transformed_B(transformed_A(source))
            phase = source_A_selecting_tail_bit(source)
            lower = constant_tail_state(
                embedded_original_state(returned_source), 1, phase
            )
            upper = constant_tail_state(
                embedded_original_state(returned_source), 2, phase
            )
            lower_expanding = transformed_A(lower)
            common_child = transformed_B(lower)
            suffix_length = alternating_suffix_length(lower_expanding)

            self.assertLess(
                constant_tail_source_coordinates(common_child)[0],
                source,
            )
            self.assertEqual(
                suffix_length >= 4,
                source % 128 in long_suffix_residues,
            )
            self.assertEqual(
                common_child < source,
                source % 128 in long_suffix_residues,
            )

            factor_three_state = transformed_A(upper)
            factor_children = transformed_moves(factor_three_state)
            factor_coordinates = [
                constant_tail_source_coordinates(child)
                for child in factor_children
            ]
            self.assertEqual(
                {coordinates[0] for coordinates in factor_coordinates},
                {common_child},
            )
            self.assertEqual(
                {coordinates[1] for coordinates in factor_coordinates},
                {0},
            )
            self.assertEqual(
                abs(factor_coordinates[0][2] - factor_coordinates[1][2]),
                1,
            )

            if suffix_length >= 4:
                self.assertEqual(
                    {
                        constant_tail_source_coordinates(child)[0]
                        for child in transformed_moves(lower_expanding)
                    },
                    {common_child},
                )

    def test_phase_match_height_descent_diamond(self) -> None:
        for source in range(1, 100000):
            if source % 32 not in {0, 10, 21, 31}:
                continue

            phase = source_A_selecting_tail_bit(source)
            first = constant_tail_state(
                embedded_original_state(source), 1, phase
            )
            first_side = transformed_B(first)
            self.assertEqual(
                first_side,
                transformed_B(transformed_A(source)),
            )
            self.assertLess(
                constant_tail_source_coordinates(first_side)[0],
                source,
            )

            second = transformed_A(first)
            lower = transformed_B(second)
            upper = transformed_A(second)
            common_child = transformed_B(lower)
            self.assertEqual(common_child, transformed_B(upper))
            self.assertLess(
                constant_tail_source_coordinates(common_child)[0],
                source,
            )

            lower_expanding = transformed_A(lower)
            if alternating_suffix_length(lower_expanding) < 3:
                continue
            for child_of_first_side in transformed_moves(first_side):
                self.assertIn(
                    common_child,
                    transformed_moves(child_of_first_side),
                )

    def test_length_two_boundary_normal_form(self) -> None:
        same_phase_residues = {10, 32, 95, 117}
        opposite_phase_residues = {31, 53, 74, 96}
        for source in range(1, 100000):
            if source % 128 not in same_phase_residues | opposite_phase_residues:
                continue

            phase = source_A_selecting_tail_bit(source)
            first = constant_tail_state(
                embedded_original_state(source), 1, phase
            )
            middle = transformed_B(first)
            second = transformed_A(first)
            lower = transformed_B(second)
            upper = transformed_A(second)
            lower_expanding = transformed_A(lower)
            common_child = transformed_B(lower)
            self.assertEqual(alternating_suffix_length(lower_expanding), 2)
            self.assertEqual(common_child, transformed_A(transformed_A(middle)))

            lifted_win_source = transformed_A(lower_expanding)
            returned_win_child = transformed_B(lower_expanding)
            self.assertEqual(
                constant_tail_source_coordinates(lifted_win_source),
                (common_child, 0, 1, phase),
            )
            self.assertIn(returned_win_child, transformed_moves(common_child))
            self.assertLess(
                constant_tail_source_coordinates(returned_win_child)[0],
                source,
            )

            other_child = next(
                child
                for child in transformed_moves(common_child)
                if child != returned_win_child
            )
            phases_match = phase == source_A_selecting_tail_bit(common_child)
            self.assertEqual(
                phases_match,
                source % 128 in same_phase_residues,
            )
            if phases_match:
                self.assertEqual(returned_win_child, transformed_A(common_child))
                self.assertEqual(other_child, transformed_B(common_child))
            else:
                self.assertEqual(returned_win_child, transformed_B(common_child))
                self.assertEqual(other_child, transformed_A(common_child))

            factor_three_state = transformed_A(upper)
            factor_children = [
                constant_tail_source_coordinates(child)
                for child in transformed_moves(factor_three_state)
            ]
            self.assertEqual(
                {coordinates[0] for coordinates in factor_children},
                {common_child},
            )
            self.assertEqual(
                {coordinates[2] for coordinates in factor_children},
                {1, 2},
            )
            self.assertEqual(
                {coordinates[3] for coordinates in factor_children},
                {1 - phase},
            )

    def test_A_selecting_lift_side_diamond(self) -> None:
        for source in range(1, 100000):
            phase = source_A_selecting_tail_bit(source)
            coefficient = embedded_original_state(source)
            lift = constant_tail_state(
                coefficient, 1, phase
            )
            upper = constant_tail_state(coefficient, 2, phase)
            selected_source = transformed_A(source)
            selected_expanding = transformed_A(selected_source)
            lifted_side = transformed_B(lift)

            self.assertEqual(
                transformed_A(lift),
                4 * selected_expanding + 1 + phase,
            )
            self.assertIn(lifted_side, transformed_moves(selected_source))
            if selected_expanding % 2 == phase:
                self.assertEqual(lifted_side, selected_expanding)
            else:
                self.assertEqual(
                    lifted_side,
                    transformed_B(selected_source),
                )

            self.assertEqual(transformed_B(upper), lifted_side)
            if lifted_side > 0:
                self.assertLess(
                    constant_tail_source_coordinates(lifted_side)[0],
                    source,
                )
                for child in transformed_moves(lifted_side):
                    if child == 0:
                        continue
                    self.assertLess(
                        constant_tail_source_coordinates(child)[0],
                        source,
                    )

            factor_state = transformed_A(upper)
            factor_coordinates = [
                constant_tail_source_coordinates(child)
                for child in transformed_moves(factor_state)
            ]
            self.assertEqual(
                {coordinates[0] for coordinates in factor_coordinates},
                {lifted_side},
            )
            self.assertEqual(
                {coordinates[1] for coordinates in factor_coordinates},
                {0},
            )
            self.assertEqual(
                abs(
                    factor_coordinates[0][2]
                    - factor_coordinates[1][2]
                ),
                1,
            )

    def test_finite_obligation_win_side_token_geometry(self) -> None:
        for source in range(1, 100000):
            phase = source_A_selecting_tail_bit(source)
            coefficient = embedded_original_state(source)
            lower = constant_tail_state(coefficient, 1, phase)
            selected_source = transformed_A(source)
            common_side = transformed_B(lower)
            returned_token = transformed_B(selected_source)

            selected_children = transformed_moves(selected_source)
            self.assertIn(common_side, selected_children)
            self.assertEqual(returned_token, transformed_B(selected_source))

            if source % 16 in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
                loss_source = transformed_B(source)
                expanding_coordinates = constant_tail_source_coordinates(
                    transformed_A(selected_source)
                )
                returned_coordinates = constant_tail_source_coordinates(
                    returned_token
                )
                self.assertEqual(
                    expanding_coordinates[:2],
                    (loss_source, 0),
                )
                self.assertEqual(
                    returned_coordinates[:2],
                    (loss_source, 0),
                )
                self.assertEqual(
                    abs(
                        expanding_coordinates[2]
                        - returned_coordinates[2]
                    ),
                    1,
                )
                self.assertEqual(
                    expanding_coordinates[3],
                    returned_coordinates[3],
                )
            else:
                self.assertIn(
                    returned_token,
                    transformed_moves(transformed_B(source)),
                )

    def test_exponent_one_factor_fork_provenance(self) -> None:
        observed_letters = set()
        for source in range(1, 100000):
            phase = source_A_selecting_tail_bit(source)
            opposite_phase = 1 - phase
            coefficient = embedded_original_state(source)
            lower = constant_tail_state(coefficient, 1, phase)
            upper = constant_tail_state(coefficient, 2, phase)
            retained_loss = transformed_A(lower)
            factor_source = transformed_B(lower)
            factor_parent = transformed_A(upper)
            factor_children = transformed_moves(factor_parent)
            factor_coordinates = [
                constant_tail_source_coordinates(child)
                for child in factor_children
            ]
            lower_exponent = min(
                coordinates[2] for coordinates in factor_coordinates
            )
            if lower_exponent != 1:
                continue

            self.assertEqual(
                factor_source,
                transformed_A(transformed_A(source)),
            )
            retained_win = transformed_B(retained_loss)
            letter, valuation, selected_loss = source_boundary_transition(
                factor_source, opposite_phase
            )
            observed_letters.add(letter)
            self.assertEqual(
                {retained_win, selected_loss},
                set(transformed_moves(factor_source)),
            )
            self.assertNotEqual(retained_win, selected_loss)
            if selected_loss > 0:
                self.assertLess(
                    constant_tail_source_coordinates(selected_loss)[0],
                    source,
                )

            common_children = set(
                transformed_moves(factor_children[0])
            ) & set(transformed_moves(factor_children[1]))
            self.assertEqual(len(common_children), 1)
            common_child = common_children.pop()

            if letter == "A":
                self.assertEqual(valuation, 1)
                self.assertIn(
                    common_child,
                    transformed_moves(selected_loss),
                )
            else:
                transferred_signed = transformed_A(
                    min(factor_children)
                )
                transferred_coordinates = {
                    constant_tail_source_coordinates(common_child),
                    constant_tail_source_coordinates(transferred_signed),
                }
                self.assertEqual(
                    {coordinates[0] for coordinates in transferred_coordinates},
                    {selected_loss},
                )
                self.assertEqual(
                    {coordinates[1] for coordinates in transferred_coordinates},
                    {0},
                )
                self.assertEqual(
                    {coordinates[2] for coordinates in transferred_coordinates},
                    {valuation - 1, valuation},
                )

        self.assertEqual(observed_letters, {"A", "B"})

    def test_higher_factor_fork_source_diamond(self) -> None:
        observed_exponents = set()
        for source in range(1, 100000):
            phase = source_A_selecting_tail_bit(source)
            coefficient = embedded_original_state(source)
            lower = constant_tail_state(coefficient, 1, phase)
            upper = constant_tail_state(coefficient, 2, phase)
            selected_source = transformed_A(source)
            factor_source = transformed_B(lower)
            factor_parent = transformed_A(upper)
            factor_coordinates = [
                constant_tail_source_coordinates(child)
                for child in transformed_moves(factor_parent)
            ]
            lower_exponent = min(
                coordinates[2] for coordinates in factor_coordinates
            )
            if lower_exponent < 2:
                continue

            observed_exponents.add(lower_exponent)
            self.assertEqual(
                factor_source,
                transformed_B(selected_source),
            )
            self.assertNotIn(
                source % 16,
                SIDE_RELATION_EXCEPTIONAL_RESIDUES,
            )
            self.assertIn(
                factor_source,
                transformed_moves(transformed_B(source)),
            )
            self.assertEqual(
                set(transformed_moves(selected_source)),
                {
                    factor_source,
                    transformed_A(selected_source),
                },
            )

        self.assertIn(2, observed_exponents)
        self.assertIn(3, observed_exponents)
        self.assertTrue(any(exponent >= 4 for exponent in observed_exponents))

    def test_B_selecting_source_frame_diamond(self) -> None:
        for source in range(1, 100000):
            phase = 1 - source_A_selecting_tail_bit(source)
            coefficient = embedded_original_state(source)
            lower = constant_tail_state(coefficient, 1, phase)
            upper = constant_tail_state(coefficient, 2, phase)
            lower_expanding = transformed_A(lower)
            common_child = transformed_B(lower)

            selected_source = transformed_B(source)
            selected_coordinates = [
                constant_tail_source_coordinates(lower_expanding),
                constant_tail_source_coordinates(common_child),
            ]
            self.assertEqual(
                {coordinates[0] for coordinates in selected_coordinates},
                {selected_source},
            )
            self.assertEqual(
                {coordinates[1] for coordinates in selected_coordinates},
                {0},
            )
            self.assertEqual(
                selected_coordinates[0][2],
                selected_coordinates[1][2] + 1,
            )

            common_grandchildren = set(
                transformed_moves(lower_expanding)
            ) & set(transformed_moves(common_child))
            self.assertEqual(len(common_grandchildren), 1)
            other_grandchild = next(
                child
                for child in transformed_moves(common_child)
                if child not in common_grandchildren
            )
            factor_three_state = transformed_A(upper)
            self.assertEqual(
                transformed_B(factor_three_state),
                other_grandchild,
            )

    def test_final_B_source_return_filter(self) -> None:
        residual_classes = {10, 31, 32, 53, 74, 95, 96, 117}
        nondecreasing_classes = {10, 31, 53, 95, 160, 202, 224, 245}
        matching_classes = {10, 31, 160, 202, 309, 351, 480, 501}

        for source in range(1, 100000):
            if source % 128 not in residual_classes:
                continue

            returned_source = transformed_B(transformed_A(source))
            common_source = transformed_A(transformed_A(returned_source))
            next_source = transformed_B(common_source)
            selecting_phase = 1 - source_A_selecting_tail_bit(common_source)
            letter, valuation, decoded_source = source_boundary_transition(
                common_source, selecting_phase
            )

            self.assertEqual(letter, "B")
            self.assertEqual(decoded_source, next_source)
            self.assertEqual(
                next_source >= source,
                source % 256 in nondecreasing_classes,
            )
            self.assertEqual(valuation == 2, next_source >= source)

            if next_source < source:
                continue
            transferred_phase = 1 - selecting_phase
            self.assertEqual(
                transferred_phase == source_A_selecting_tail_bit(next_source),
                source % 512 in matching_classes,
            )

    def test_final_B_transfer_run_is_bounded(self) -> None:
        nondecreasing_classes = {10, 31, 53, 95, 160, 202, 224, 245}

        for source in range(1, 100000):
            if source % 256 not in nondecreasing_classes:
                continue

            returned_source = transformed_B(transformed_A(source))
            common_source = transformed_A(transformed_A(returned_source))
            current = transformed_B(common_source)
            phase = source_A_selecting_tail_bit(common_source)
            self.assertLess(current, 2 * source)

            surviving_B_transfers = 0
            while phase != source_A_selecting_tail_bit(current):
                letter, valuation, following = source_boundary_transition(
                    current, phase
                )
                self.assertEqual(letter, "B")
                if valuation >= 3:
                    self.assertLess(following, source)
                    break

                self.assertEqual(valuation, 2)
                if following < source:
                    break
                surviving_B_transfers += 1
                self.assertLessEqual(surviving_B_transfers, 2)
                current = following
                phase = 1 - phase
            else:
                self.assertGreaterEqual(current, source)

            if phase != source_A_selecting_tail_bit(current):
                continue

            coefficient = embedded_original_state(current)
            lower = constant_tail_state(coefficient, 1, phase)
            upper = constant_tail_state(coefficient, 2, phase)
            lifted_side = transformed_B(lower)
            factor_three_state = transformed_A(upper)
            selected_lift = transformed_A(lower)
            factor_coordinates = [
                constant_tail_source_coordinates(child)
                for child in transformed_moves(factor_three_state)
            ]
            self.assertEqual(
                {coordinates[0] for coordinates in factor_coordinates},
                {lifted_side},
            )
            self.assertEqual(
                {coordinates[1] for coordinates in factor_coordinates},
                {0},
            )
            self.assertEqual(
                factor_coordinates[0][2],
                factor_coordinates[1][2] + 1,
            )
            if lifted_side >= source:
                self.assertLessEqual(factor_coordinates[1][2], 3)

            lower_exponent = factor_coordinates[1][2]
            if lower_exponent == 1:
                self.assertEqual(
                    lifted_side,
                    transformed_A(transformed_A(current)),
                )
            else:
                self.assertEqual(
                    lifted_side,
                    transformed_B(transformed_A(current)),
                )
                self.assertNotIn(
                    current % 16,
                    SIDE_RELATION_EXCEPTIONAL_RESIDUES,
                )
            opposite_twin = transformed_B(factor_three_state)
            selected_twin = transformed_A(selected_lift)
            self.assertEqual(
                constant_tail_source_coordinates(opposite_twin),
                (lifted_side, 0, lower_exponent, 1 - phase),
            )
            self.assertEqual(
                constant_tail_source_coordinates(selected_twin),
                (lifted_side, 0, lower_exponent, phase),
            )

            frame_upper, frame_lower = transformed_moves(factor_three_state)
            common_frame_children = set(transformed_moves(frame_upper)) & set(
                transformed_moves(frame_lower)
            )
            self.assertEqual(len(common_frame_children), 1)
            common_frame_child = next(iter(common_frame_children))

            if lower_exponent == 1:
                self.assertEqual(
                    common_frame_child,
                    transformed_B(frame_lower),
                )
                self.assertEqual(
                    common_frame_child,
                    transformed_B(frame_upper),
                )

                factor_source = lifted_side
                self.assertEqual(
                    factor_source,
                    transformed_A(transformed_A(current)),
                )
                factor_phase = 1 - phase
                letter, valuation, selected_at_factor_source = (
                    source_boundary_transition(
                        factor_source,
                        factor_phase,
                    )
                )
                unselected_at_factor_source = next(
                    child
                    for child in transformed_moves(factor_source)
                    if child != selected_at_factor_source
                )
                self.assertEqual(
                    transformed_B(selected_lift),
                    unselected_at_factor_source,
                )

                if letter == "A":
                    self.assertIn(
                        common_frame_child,
                        transformed_moves(selected_at_factor_source),
                    )
                else:
                    selected_source = transformed_A(current)
                    hidden_return = transformed_B(selected_source)
                    self.assertNotIn(
                        current % 16,
                        SIDE_RELATION_EXCEPTIONAL_RESIDUES,
                    )
                    if (
                        selected_source % 16
                        in SIDE_RELATION_EXCEPTIONAL_RESIDUES
                    ):
                        self.assertEqual(valuation, 2)
                        self.assertEqual(
                            constant_tail_source_coordinates(
                                selected_at_factor_source
                            )[:2],
                            (hidden_return, 0),
                        )
                    else:
                        self.assertGreaterEqual(valuation, 3)
                        self.assertIn(
                            selected_at_factor_source,
                            transformed_moves(hidden_return),
                        )

                transferred_source = constant_tail_source_coordinates(
                    common_frame_child
                )[0]
                if factor_phase == source_A_selecting_tail_bit(factor_source):
                    self.assertLess(transferred_source, current)
                else:
                    letter, valuation, selected_source = (
                        source_boundary_transition(
                            factor_source,
                            factor_phase,
                        )
                    )
                    self.assertEqual(letter, "B")
                    self.assertEqual(transferred_source, selected_source)
                    if selected_source >= source:
                        self.assertIn(valuation, {2, 3})
                    self.assertEqual(
                        constant_tail_source_coordinates(
                            common_frame_child
                        ),
                        (
                            selected_source,
                            0,
                            valuation - 1,
                            phase,
                        ),
                    )
                    if valuation == 3:
                        returned_common = transformed_B(
                            common_frame_child
                        )
                        if returned_common > 0:
                            returned_common_source = (
                                constant_tail_source_coordinates(
                                    returned_common
                                )[0]
                            )
                            self.assertLessEqual(
                                4 * returned_common_source,
                                3 * selected_source + 1,
                            )
                    self.assertLessEqual(
                        selected_source,
                        (27 * current + 19) // (1 << (valuation + 2)),
                    )
                    if valuation >= 4:
                        self.assertLess(selected_source, source)
                continue

            factor_coefficient = embedded_original_state(lifted_side)
            expected_common = constant_tail_state(
                3 * factor_coefficient,
                lower_exponent - 1,
                1 - phase,
            )
            expected_twin = constant_tail_state(
                3 * factor_coefficient,
                lower_exponent - 1,
                phase,
            )
            self.assertEqual(common_frame_child, expected_common)
            self.assertEqual(transformed_A(selected_twin), expected_twin)
            self.assertEqual(abs(expected_common - expected_twin), 1)

            selected_prefix = transformed_B(selected_lift)
            self.assertEqual(
                selected_prefix,
                constant_tail_state(
                    factor_coefficient,
                    lower_exponent - 1,
                    phase,
                ),
            )

            if lifted_side < source or lower_exponent > 3:
                continue

            factor_coefficient = embedded_original_state(lifted_side)
            if lower_exponent == 2:
                boundary = common_frame_child
                boundary_source, boundary_power, boundary_exponent, _ = (
                    constant_tail_source_coordinates(transformed_A(boundary))
                )
                self.assertEqual(boundary_power, 0)
                if boundary_exponent >= 5:
                    self.assertLess(boundary_source, source)
                if boundary_exponent == 2:
                    expanding_boundary, contracting_boundary = (
                        transformed_moves(boundary)
                    )
                    self.assertEqual(
                        constant_tail_source_coordinates(
                            expanding_boundary
                        ),
                        (
                            boundary_source,
                            0,
                            2,
                            phase,
                        ),
                    )
                    self.assertEqual(
                        constant_tail_source_coordinates(
                            contracting_boundary
                        ),
                        (
                            boundary_source,
                            0,
                            1,
                            phase,
                        ),
                    )
                    self.assertLess(
                        16 * boundary_source,
                        81 * source,
                    )
                if boundary_exponent == 1:
                    canonical_lift = transformed_A(boundary)
                    raw_side = transformed_B(boundary)
                    self.assertEqual(
                        constant_tail_source_coordinates(canonical_lift),
                        (
                            boundary_source,
                            0,
                            1,
                            phase,
                        ),
                    )
                    self.assertEqual(
                        raw_side,
                        alternating_suffix_remainder(canonical_lift),
                    )
                    self.assertLess(
                        8 * boundary_source,
                        81 * source,
                    )
                    if raw_side > 0:
                        raw_source = constant_tail_source_coordinates(
                            raw_side
                        )[0]
                        self.assertLess(
                            96 * raw_source,
                            243 * source + 4,
                        )
                if boundary_exponent >= 3:
                    boundary_coefficient = embedded_original_state(
                        boundary_source
                    )
                    if selected_twin % 16 in {
                        1,
                        3,
                        12,
                        14,
                    }:
                        self.assertIn(selected_twin % 16, {3, 12})
                        exceptional_loss = transformed_B(selected_twin)
                        exceptional_lift = transformed_B(expected_twin)
                        (
                            exceptional_source,
                            exceptional_power,
                            exceptional_exponent,
                            exceptional_phase,
                        ) = constant_tail_source_coordinates(
                            exceptional_lift
                        )
                        self.assertEqual(
                            (
                                exceptional_source,
                                exceptional_power,
                                exceptional_phase,
                            ),
                            (
                                exceptional_loss,
                                0,
                                1 - phase,
                            ),
                        )
                        self.assertLess(
                            16 * exceptional_loss,
                            81 * source,
                        )
                        if exceptional_loss >= source:
                            self.assertLessEqual(
                                exceptional_exponent,
                                3,
                            )
                    if selected_twin % 16 not in {
                        1,
                        3,
                        12,
                        14,
                    }:
                        self.assertIn(
                            transformed_B(expected_twin),
                            transformed_moves(
                                transformed_B(selected_twin)
                            ),
                        )
                    self.assertEqual(
                        transformed_B(expected_twin),
                        constant_tail_state(
                            boundary_coefficient,
                            boundary_exponent - 2,
                            phase,
                        ),
                    )
                    expanding_boundary, contracting_boundary = (
                        transformed_moves(boundary)
                    )
                    self.assertEqual(
                        constant_tail_source_coordinates(
                            expanding_boundary
                        ),
                        (
                            boundary_source,
                            0,
                            boundary_exponent,
                            phase,
                        ),
                    )
                    self.assertEqual(
                        constant_tail_source_coordinates(
                            contracting_boundary
                        ),
                        (
                            boundary_source,
                            0,
                            boundary_exponent - 1,
                            phase,
                        ),
                    )
            else:
                first_boundary = constant_tail_state(
                    3 * factor_coefficient,
                    1,
                    1 - phase,
                )
                first_source, first_power, first_exponent, _ = (
                    constant_tail_source_coordinates(
                        transformed_A(first_boundary)
                    )
                )
                self.assertEqual(first_power, 0)
                if first_exponent >= 4:
                    self.assertLess(first_source, source)
                contracting_boundary = transformed_B(common_frame_child)
                if first_exponent >= 2:
                    self.assertEqual(
                        constant_tail_source_coordinates(
                            contracting_boundary
                        ),
                        (
                            first_source,
                            0,
                            first_exponent - 1,
                            phase,
                        ),
                    )
                    if first_exponent == 2:
                        self.assertLess(
                            96 * first_source,
                            243 * source + 44,
                        )
                    elif first_exponent == 3:
                        self.assertLess(
                            192 * first_source,
                            243 * source + 44,
                        )
                elif first_exponent == 1:
                    canonical_boundary = transformed_A(first_boundary)
                    self.assertEqual(
                        contracting_boundary,
                        alternating_suffix_remainder(
                            canonical_boundary
                        ),
                    )
                    self.assertLess(
                        48 * first_source,
                        243 * source + 44,
                    )
                    if contracting_boundary > 0:
                        contracting_source = (
                            constant_tail_source_coordinates(
                                contracting_boundary
                            )[0]
                        )
                        self.assertLess(
                            192 * contracting_source,
                            243 * source + 44,
                        )

                second_boundary = transformed_A(common_frame_child)
                second_source, second_power, second_exponent, _ = (
                    constant_tail_source_coordinates(
                        transformed_A(second_boundary)
                    )
                )
                self.assertEqual(second_power, 0)
                if second_exponent >= 5:
                    self.assertLess(second_source, source)
                self.assertLess(
                    24 * (1 << second_exponent) * second_source,
                    729 * source + 116,
                )
                expanding_second, contracting_second = transformed_moves(
                    second_boundary
                )
                if second_exponent >= 2:
                    self.assertEqual(
                        constant_tail_source_coordinates(
                            expanding_second
                        ),
                        (
                            second_source,
                            0,
                            second_exponent,
                            phase,
                        ),
                    )
                    self.assertEqual(
                        constant_tail_source_coordinates(
                            contracting_second
                        ),
                        (
                            second_source,
                            0,
                            second_exponent - 1,
                            phase,
                        ),
                    )
                elif second_exponent == 1:
                    canonical_second = transformed_A(second_boundary)
                    self.assertEqual(
                        contracting_second,
                        alternating_suffix_remainder(canonical_second),
                    )
                    if contracting_second > 0:
                        second_raw_source = (
                            constant_tail_source_coordinates(
                                contracting_second
                            )[0]
                        )
                        self.assertLess(
                            192 * second_raw_source,
                            729 * source + 116,
                        )

                if first_exponent >= 4:
                    self.assertLess(first_source, source)
                    self.assertEqual(second_exponent, 1)
                    self.assertLess(second_source, 16 * source)
                    self.assertNotEqual(
                        phase,
                        source_A_selecting_tail_bit(second_source),
                    )
                    self.assertEqual(
                        second_source,
                        constant_tail_state(
                            embedded_original_state(first_source),
                            first_exponent - 1,
                            phase,
                        ),
                    )
                    self.assertEqual(
                        constant_tail_source_coordinates(
                            transformed_B(second_boundary)
                        ),
                        (
                            first_source,
                            1,
                            first_exponent - 3,
                            phase,
                        ),
                    )

                    contracting_win = transformed_B(common_frame_child)
                    returned_win = transformed_B(second_boundary)
                    self.assertEqual(
                        returned_win,
                        transformed_B(second_source),
                    )
                    self.assertEqual(
                        source_boundary_transition(second_source, phase),
                        ("B", 2, returned_win),
                    )
                    self.assertEqual(
                        transformed_B(contracting_win),
                        returned_win,
                    )
                    loss_sibling = transformed_A(contracting_win)
                    lower_common = set(transformed_moves(loss_sibling)) & set(
                        transformed_moves(returned_win)
                    )
                    self.assertEqual(len(lower_common), 1)
                    self.assertEqual(
                        next(iter(lower_common)),
                        transformed_B(transformed_A(second_source)),
                    )
                    selected_letter, selected_valuation, selected_win = (
                        source_boundary_transition(
                            returned_win,
                            1 - phase,
                        )
                    )
                    self.assertEqual(
                        selected_letter,
                        "B" if first_exponent == 4 else "A",
                    )
                    self.assertEqual(
                        selected_win,
                        next(iter(lower_common)),
                    )

                    loss_child = next(
                        child
                        for child in transformed_moves(returned_win)
                        if child != selected_win
                    )
                    lift = constant_tail_state(
                        embedded_original_state(returned_win),
                        1,
                        1 - phase,
                    )
                    lifted_side = transformed_B(lift)

                    if first_exponent == 4:
                        if selected_valuation >= 6:
                            self.assertLess(selected_win, source)
                        if selected_valuation == 2:
                            selected_coefficient = embedded_original_state(
                                selected_win
                            )
                            exponent_zero_win = transformed_A(loss_child)
                            returned_source_win = transformed_B(loss_child)
                            self.assertEqual(
                                exponent_zero_win,
                                selected_coefficient - phase,
                            )
                            self.assertEqual(
                                returned_source_win,
                                alternating_suffix_remainder(
                                    exponent_zero_win
                                ),
                            )
                            self.assertNotIn(
                                returned_win % 16,
                                {1, 3, 12, 14},
                            )
                            self.assertIn(
                                returned_win % 16,
                                {2, 5, 10, 13},
                            )
                            self.assertEqual(
                                source_boundary_transition(
                                    selected_win,
                                    phase,
                                )[2],
                                returned_source_win,
                            )
                            if (
                                phase
                                == source_A_selecting_tail_bit(
                                    selected_win
                                )
                            ):
                                lifted_common = transformed_B(
                                    constant_tail_state(
                                        selected_coefficient,
                                        1,
                                        phase,
                                    )
                                )
                                self.assertIn(
                                    lifted_common,
                                    transformed_moves(
                                        returned_source_win
                                    ),
                                )
                            if selected_win >= source:
                                self.assertLess(selected_win, 10 * source)
                                bounded_source = selected_win
                                bounded_phase = phase
                                surviving_valuation_two = 0
                                while (
                                    bounded_phase
                                    != source_A_selecting_tail_bit(
                                        bounded_source
                                    )
                                ):
                                    (
                                        bounded_letter,
                                        bounded_valuation,
                                        following_source,
                                    ) = source_boundary_transition(
                                        bounded_source,
                                        bounded_phase,
                                    )
                                    self.assertEqual(bounded_letter, "B")
                                    if following_source < source:
                                        break
                                    self.assertLessEqual(
                                        bounded_valuation,
                                        4,
                                    )
                                    if bounded_valuation != 2:
                                        break
                                    surviving_valuation_two += 1
                                    self.assertLessEqual(
                                        surviving_valuation_two,
                                        8,
                                    )
                                    bounded_source = following_source
                                    bounded_phase = 1 - bounded_phase
                        if selected_valuation >= 3:
                            selected_coefficient = embedded_original_state(
                                selected_win
                            )
                            upper_high = constant_tail_state(
                                selected_coefficient,
                                selected_valuation,
                                phase,
                            )
                            upper_low = constant_tail_state(
                                selected_coefficient,
                                selected_valuation - 1,
                                phase,
                            )
                            first_lower = constant_tail_state(
                                selected_coefficient,
                                1,
                                phase,
                            )
                            second_lower = constant_tail_state(
                                selected_coefficient,
                                2,
                                phase,
                            )
                            if first_lower % 16 in {1, 3, 12, 14}:
                                self.assertIn(first_lower % 16, {1, 14})
                            if second_lower % 16 in {1, 3, 12, 14}:
                                self.assertIn(second_lower % 16, {3, 12})
                            self.assertNotIn(
                                constant_tail_state(
                                    selected_coefficient,
                                    3,
                                    phase,
                                )
                                % 16,
                                {1, 3, 12, 14},
                            )
                            if (
                                selected_win >= source
                                and selected_valuation == 3
                                and first_lower % 16
                                in {1, 3, 12, 14}
                            ):
                                first_side = transformed_B(first_lower)
                                if first_side > 0:
                                    self.assertLess(
                                        constant_tail_source_coordinates(
                                            first_side
                                        )[0],
                                        source,
                                    )
                            if second_lower % 16 in {3, 12}:
                                exceptional_side = transformed_B(
                                    transformed_A(second_lower)
                                )
                                common_loss = transformed_B(second_lower)
                                (
                                    exceptional_source,
                                    exceptional_power,
                                    exceptional_exponent,
                                    exceptional_phase,
                                ) = constant_tail_source_coordinates(
                                    exceptional_side
                                )
                                self.assertEqual(
                                    (
                                        exceptional_source,
                                        exceptional_power,
                                        exceptional_phase,
                                    ),
                                    (common_loss, 0, 1 - phase),
                                )
                                if (
                                    selected_win >= source
                                    and common_loss >= source
                                ):
                                    if selected_valuation == 3:
                                        self.assertLessEqual(
                                            exceptional_exponent,
                                            4,
                                        )
                                    elif selected_valuation == 4:
                                        self.assertLessEqual(
                                            exceptional_exponent,
                                            3,
                                        )
                            upper_common = set(
                                transformed_moves(upper_high)
                            ) & set(transformed_moves(upper_low))
                            self.assertEqual(
                                upper_common,
                                {
                                    constant_tail_state(
                                        3 * selected_coefficient,
                                        selected_valuation - 2,
                                        phase,
                                    )
                                },
                            )
                            self.assertEqual(
                                constant_tail_source_coordinates(
                                    transformed_A(loss_child)
                                ),
                                (
                                    selected_win,
                                    0,
                                    selected_valuation - 2,
                                    phase,
                                ),
                            )
                        if selected_valuation >= 4:
                            self.assertEqual(
                                constant_tail_source_coordinates(
                                    transformed_B(loss_child)
                                ),
                                (
                                    selected_win,
                                    0,
                                    selected_valuation - 3,
                                    phase,
                                ),
                            )
                    elif first_exponent == 5:
                        self.assertEqual(
                            lifted_side,
                            transformed_A(selected_win),
                        )
                        loss_source, loss_power, loss_exponent, _ = (
                            constant_tail_source_coordinates(lifted_side)
                        )
                        self.assertEqual(loss_source, loss_child)
                        self.assertEqual(loss_power, 0)
                        if loss_exponent >= 4:
                            self.assertLess(loss_source, source)
                        if returned_win % 16 in {1, 3, 12, 14}:
                            self.assertIn(returned_win % 16, {3, 12})
                            self.assertGreaterEqual(loss_exponent, 2)
                            side_loss = transformed_B(selected_win)
                            self.assertNotIn(
                                selected_win % 16,
                                {1, 3, 12, 14},
                            )
                            self.assertIn(
                                transformed_B(lifted_side),
                                transformed_moves(side_loss),
                            )
                        else:
                            self.assertIn(
                                transformed_B(selected_win),
                                transformed_moves(loss_child),
                            )
                    else:
                        self.assertEqual(
                            lifted_side,
                            transformed_B(selected_win),
                        )
                        self.assertIn(
                            lifted_side,
                            transformed_moves(loss_child),
                        )

    def test_height_one_arithmetic(self) -> None:
        for q in range(1, 100000):
            if transformed_B(q) == 0:
                self.assertIn(q % 16, {1, 3, 12, 14})
            if transformed_B(transformed_A(q)) == 0:
                self.assertGreater(transformed_B(q), 0)
                self.assertEqual(transformed_B(transformed_B(q)), 0)

    def test_height_one_boundary_parent_fork_arithmetic(self) -> None:
        for parent in range(1, 100000):
            endpoint = transformed_B(parent)
            if endpoint == 0 or transformed_B(endpoint) != 0:
                continue

            draw_sibling = transformed_A(parent)
            side = transformed_B(draw_sibling)
            continuation = transformed_A(draw_sibling)
            if parent % 16 not in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
                self.assertIn(side, (0, transformed_A(endpoint)))
                continue

            side_coordinates = constant_tail_source_coordinates(side)
            continuation_coordinates = constant_tail_source_coordinates(
                continuation
            )
            self.assertEqual(side_coordinates[:2], (endpoint, 0))
            self.assertEqual(continuation_coordinates[:2], (endpoint, 0))
            self.assertEqual(
                continuation_coordinates[2], side_coordinates[2] + 1
            )
            self.assertEqual(continuation_coordinates[3], side_coordinates[3])

    def test_height_one_ordinary_successor_four_rows(self) -> None:
        expected = {
            (3, 1, 7, 11),
            (12, 1, 8, 4),
            (1, 2, 6, 9),
            (14, 2, 9, 6),
        }
        seen: set[tuple[int, int, int, int]] = set()
        for parent in range(1, 100000):
            if parent % 16 in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
                continue
            endpoint = transformed_B(parent)
            if endpoint == 0 or transformed_B(endpoint) != 0:
                continue

            spine = transformed_A(parent)
            lifted_endpoint = transformed_A(endpoint)
            if transformed_B(spine) != lifted_endpoint:
                continue

            continuation = transformed_A(spine)
            row = (
                endpoint % 16,
                alternating_suffix_length(spine),
                spine % 16,
                continuation % 16,
            )
            self.assertIn(row, expected)
            self.assertNotIn(
                spine % 16, SIDE_RELATION_EXCEPTIONAL_RESIDUES
            )
            self.assertNotIn(
                continuation % 16,
                SIDE_RELATION_EXCEPTIONAL_RESIDUES,
            )
            seen.add(row)
        self.assertEqual(seen, expected)

    def test_height_one_endpoint_has_adjacent_zero_source_children(self) -> None:
        for endpoint in range(1, 100000):
            if transformed_B(endpoint) != 0:
                continue
            lifted_endpoint = transformed_A(endpoint)
            upper, lower = transformed_moves(lifted_endpoint)
            upper_coordinates = constant_tail_source_coordinates(upper)
            lower_coordinates = constant_tail_source_coordinates(lower)
            self.assertEqual(upper_coordinates[:2], (0, 0))
            self.assertEqual(lower_coordinates[:2], (0, 0))
            self.assertEqual(upper_coordinates[2], lower_coordinates[2] + 1)
            self.assertEqual(upper_coordinates[3], lower_coordinates[3])

    def test_height_one_source_has_dyadic_signed_transition(self) -> None:
        for source in range(1, 100000):
            if transformed_B(source) != 0:
                continue
            alternating = transformed_A(source)
            length = alternating.bit_length()
            phase = 0 if length % 2 else 1
            self.assertEqual(source_A_selecting_tail_bit(source), phase)
            self.assertEqual(
                3 * embedded_original_state(source),
                2 ** (length + 2) + 1 - 2 * phase,
            )

            letter, valuation, child_source = source_boundary_transition(
                source, phase
            )
            self.assertEqual((letter, valuation, child_source), (
                "A",
                1,
                alternating,
            ))

            letter, valuation, child_source = source_boundary_transition(
                source, 1 - phase
            )
            self.assertEqual((letter, valuation, child_source), (
                "B",
                length + 2,
                0,
            ))

    def test_height_one_factor_transition_valuation_filter(self) -> None:
        for source in range(1, 10000):
            if transformed_B(source) != 0:
                continue
            length = transformed_A(source).bit_length()
            source_phase = 0 if length % 2 else 1
            dyadic_exponent = length + 2
            coefficient = embedded_original_state(source)

            for factor_exponent in range(1, 257):
                a_value = (
                    3 ** (factor_exponent + 1) * coefficient
                    + 1
                    - 2 * source_phase
                )
                a_valuation = v2(a_value)
                self.assertEqual(
                    a_valuation,
                    2 if factor_exponent % 2 else 1,
                )

                b_phase = 1 - source_phase
                b_value = (
                    3 ** (factor_exponent + 1) * coefficient
                    + 1
                    - 2 * b_phase
                )
                b_valuation = v2(b_value)
                three_valuation = (
                    1
                    if factor_exponent % 2
                    else 2 + v2(factor_exponent)
                )
                if three_valuation < dyadic_exponent:
                    self.assertEqual(b_valuation, three_valuation)
                elif three_valuation > dyadic_exponent:
                    self.assertEqual(b_valuation, dyadic_exponent)
                else:
                    self.assertGreater(
                        b_valuation, dyadic_exponent
                    )

    def test_zero_source_factor_boundary_valuations(self) -> None:
        for power in range(1, 100):
            coefficient = 3 ** (power - 1)
            for phase in (0, 1):
                lower = constant_tail_state(coefficient, 1, phase)
                upper = constant_tail_state(coefficient, 2, phase)
                common = alternating_suffix_remainder(3**power - phase)
                signed_value = 3**power + 1 - 2 * phase
                valuation = v2(signed_value)
                signed_coefficient = signed_value >> valuation
                signed_state = constant_tail_state(
                    signed_coefficient, valuation, 1 - phase
                )

                self.assertEqual(transformed_B(lower), common)
                self.assertEqual(transformed_B(upper), common)
                self.assertEqual(transformed_A(lower), signed_state)
                next_lower = constant_tail_state(
                    3 * coefficient, 1, phase
                )
                self.assertEqual(transformed_A(upper), next_lower)
                self.assertEqual(
                    transformed_B(next_lower),
                    alternating_suffix_remainder(
                        3 ** (power + 1) - phase
                    ),
                )

                if phase == 0:
                    expected = 2 if power % 2 else 1
                else:
                    expected = 1 if power % 2 else 2 + v2(power)
                self.assertEqual(valuation, expected)

    def test_zero_source_boundary_source_coupling(self) -> None:
        for power in range(2, 100):
            for phase in (0, 1):
                signed_value = 3**power + 1 - 2 * phase
                valuation = v2(signed_value)
                coefficient = signed_value >> valuation
                source, factor_exponent = constant_tail_coefficient_source(
                    coefficient
                )
                self.assertEqual(factor_exponent, 0)

                common = alternating_suffix_remainder(3**power - phase)
                signed_state = constant_tail_state(
                    coefficient, valuation, 1 - phase
                )

                if valuation >= 2:
                    self.assertEqual(
                        common,
                        constant_tail_state(
                            coefficient, valuation - 1, 1 - phase
                        ),
                    )
                    self.assertEqual(
                        constant_tail_source_coordinates(common),
                        (source, 0, valuation - 1, 1 - phase),
                    )
                    self.assertEqual(
                        constant_tail_source_coordinates(signed_state),
                        (source, 0, valuation, 1 - phase),
                    )
                else:
                    self.assertEqual(
                        source, (3 ** (power - 1) - 1) // 2
                    )
                    selected = (
                        transformed_A(source)
                        if phase == 0
                        else transformed_B(source)
                    )
                    self.assertEqual(common, selected)
                    self.assertLess(
                        constant_tail_source_coordinates(common)[0],
                        source,
                    )

    def test_zero_source_loss_token_boundary_transport(self) -> None:
        for factor_exponent in range(9):
            coefficient = 3**factor_exponent
            for exponent in range(4, 21):
                for phase in (0, 1):
                    loss_token = constant_tail_state(
                        coefficient, exponent, phase
                    )
                    selected_win = transformed_A(loss_token)
                    self.assertEqual(
                        selected_win,
                        constant_tail_state(
                            3 * coefficient, exponent - 1, phase
                        ),
                    )
                    self.assertEqual(
                        transformed_A(selected_win),
                        constant_tail_state(
                            9 * coefficient, exponent - 2, phase
                        ),
                    )
                    self.assertEqual(
                        transformed_B(selected_win),
                        constant_tail_state(
                            9 * coefficient, exponent - 3, phase
                        ),
                    )

        for blocks in range(20):
            factor_exponent = 2 * blocks
            coefficient = 3**factor_exponent
            for phase in (0, 1):
                exponent_one = constant_tail_state(
                    coefficient, 1, phase
                )
                odd_power = factor_exponent + 1
                odd_signed = 3**odd_power + 1 - 2 * phase
                odd_valuation = v2(odd_signed)
                self.assertEqual(
                    transformed_B(exponent_one),
                    alternating_suffix_remainder(
                        3**odd_power - phase
                    ),
                )
                self.assertEqual(
                    odd_valuation, 2 if phase == 0 else 1
                )

                for terminal_exponent in (2, 3):
                    terminal = constant_tail_state(
                        coefficient, terminal_exponent, phase
                    )
                    boundary_parent = (
                        transformed_A(terminal)
                        if terminal_exponent == 2
                        else transformed_B(terminal)
                    )
                    expected_parent = constant_tail_state(
                        3 * coefficient, 1, phase
                    )
                    self.assertEqual(boundary_parent, expected_parent)

                    even_power = factor_exponent + 2
                    even_signed = 3**even_power + 1 - 2 * phase
                    even_valuation = v2(even_signed)
                    even_coefficient = even_signed >> even_valuation
                    self.assertEqual(
                        transformed_A(boundary_parent),
                        constant_tail_state(
                            even_coefficient,
                            even_valuation,
                            1 - phase,
                        ),
                    )
                    self.assertEqual(
                        transformed_B(boundary_parent),
                        alternating_suffix_remainder(
                            3**even_power - phase
                        ),
                    )
                    expected_valuation = (
                        1
                        if phase == 0
                        else 2 + v2(even_power)
                    )
                    self.assertEqual(
                        even_valuation, expected_valuation
                    )

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
