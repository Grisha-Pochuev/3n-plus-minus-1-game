from __future__ import annotations

import unittest

from src.optimal_3n1.game import (
    SIDE_RELATION_EXCEPTIONAL_RESIDUES,
    constant_tail_coefficient_source,
    constant_tail_state,
    embedded_original_state,
    source_A_selecting_tail_bit,
    transformed_A,
    transformed_B,
    transformed_moves,
    v2,
)


class AlthoeferClosureTests(unittest.TestCase):
    def test_base_phase_valuation_and_raw_attachment(self) -> None:
        """Regression support for the closure addendum's base split.

        The mathematical proof is in docs/althoefer-audit-closure.md.  This
        test checks the exact identities over a substantial finite prefix.
        """
        for source in range(1, 10_000):
            coefficient = embedded_original_state(source)
            a_phase = source_A_selecting_tail_bit(source)

            for phase in (0, 1):
                p = constant_tail_state(coefficient, 1, phase)
                u = constant_tail_state(coefficient, 2, phase)
                common = transformed_B(p)
                self.assertEqual(transformed_B(u), common)

                factor_one = transformed_A(u)
                signed_numerator = 9 * coefficient + 1 - 2 * phase
                valuation = v2(signed_numerator)
                self.assertEqual(
                    signed_numerator >> valuation,
                    embedded_original_state(common),
                )

                if phase != a_phase:
                    # B-selecting input: the next factor valuation is exactly
                    # one, and its raw child is an actual ordinary child of
                    # the exposed WIN source common.
                    self.assertEqual(valuation, 1)
                    raw = transformed_B(factor_one)
                    self.assertIn(raw, transformed_moves(common))

                    if (
                        common % 16 in SIDE_RELATION_EXCEPTIONAL_RESIDUES
                        and raw == transformed_B(common)
                        and raw > 0
                    ):
                        returned_source = constant_tail_coefficient_source(raw)[0]
                        self.assertLess(returned_source, source)
                else:
                    # A-selecting input: valuation is at least two.  Every
                    # valuation >=4 forces the returned factor-free source
                    # strictly below the old source.
                    self.assertGreaterEqual(valuation, 2)
                    if valuation >= 4:
                        self.assertLess(common, source)
                    if valuation == 3:
                        # Output phase is 1-phase; this is exactly the
                        # congruence required by Section 89.
                        output_phase = 1 - phase
                        returned_coefficient = embedded_original_state(common)
                        self.assertEqual(
                            returned_coefficient % 3,
                            (1 + output_phase) % 3,
                        )


if __name__ == "__main__":
    unittest.main()
