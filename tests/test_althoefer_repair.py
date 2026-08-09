from __future__ import annotations

import unittest

from src.optimal_3n1.game import (
    constant_tail_state,
    embedded_original_state,
    transformed_A,
    transformed_B,
    v2,
)


class AlthoeferAuditRepairTests(unittest.TestCase):
    def test_first_factor_signed_exit_is_anchored_at_common_win_source(self) -> None:
        """Regression for the exact Section 137 base-boundary identity.

        This is supporting computation only; the proof in verified-results.md
        derives the identity from Sections 14 and 18.
        """
        for source in range(0, 10_000):
            coefficient = embedded_original_state(source)
            for phase in (0, 1):
                p = constant_tail_state(coefficient, 1, phase)
                u = constant_tail_state(coefficient, 2, phase)
                common = transformed_B(p)
                self.assertEqual(transformed_B(u), common)

                signed = 9 * coefficient + 1 - 2 * phase
                valuation = v2(signed)
                self.assertEqual(
                    signed >> valuation,
                    embedded_original_state(common),
                )

                factor_one = transformed_A(u)
                signed_exit = transformed_A(factor_one)
                self.assertEqual(
                    signed_exit,
                    constant_tail_state(
                        embedded_original_state(common),
                        valuation,
                        1 - phase,
                    ),
                )


if __name__ == "__main__":
    unittest.main()
