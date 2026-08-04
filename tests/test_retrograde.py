import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from optimal_3n1.game import transformed_A, transformed_moves  # noqa: E402
from optimal_3n1.retrograde import (  # noqa: E402
    Outcome,
    bounded_retrograde,
    certified_finite_draw_kernel,
)


class RetrogradeTests(unittest.TestCase):
    def test_terminal(self) -> None:
        result = bounded_retrograde(100)
        self.assertEqual(result.outcome(0), Outcome.LOSS)

    def test_every_proved_win_has_proved_loss_child(self) -> None:
        result = bounded_retrograde(10000)
        for q in range(1, result.limit + 1):
            if result.outcome(q) == Outcome.WIN:
                children = transformed_moves(q)
                self.assertTrue(
                    any(child <= result.limit and result.outcome(child) == Outcome.LOSS for child in children)
                )

    def test_every_proved_loss_has_two_proved_win_children(self) -> None:
        result = bounded_retrograde(10000)
        for q in range(1, result.limit + 1):
            if result.outcome(q) == Outcome.LOSS:
                children = transformed_moves(q)
                self.assertTrue(all(child <= result.limit for child in children))
                self.assertTrue(all(result.outcome(child) == Outcome.WIN for child in children))

    def test_proof_children_strictly_precede_parent(self) -> None:
        result = bounded_retrograde(10000)
        for q in range(result.limit + 1):
            if result.outcome(q) == Outcome.UNKNOWN:
                continue
            for child in result.proof_children(q):
                self.assertLess(result.resolved_at[child], result.resolved_at[q])

    def test_no_four_consecutive_wins_on_an_A_ray(self) -> None:
        result = bounded_retrograde(10000)
        for q in range(1, 1000):
            ray = [q]
            for _ in range(3):
                ray.append(transformed_A(ray[-1]))
            self.assertFalse(all(result.outcome(node) == Outcome.WIN for node in ray))

    def test_no_certified_finite_draw_kernel_at_small_cutoff(self) -> None:
        result = bounded_retrograde(10000)
        self.assertEqual(list(certified_finite_draw_kernel(result)), [])


if __name__ == "__main__":
    unittest.main()
