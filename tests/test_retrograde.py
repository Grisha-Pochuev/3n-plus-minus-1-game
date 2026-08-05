import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from optimal_3n1.game import (  # noqa: E402
    SIDE_RELATION_EXCEPTIONAL_RESIDUES,
    transformed_A,
    transformed_B,
    transformed_moves,
)
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

    def test_nonexceptional_win_path_two_step_target(self) -> None:
        result = bounded_retrograde(10000)
        for q in range(1, 1000):
            if q % 16 in SIDE_RELATION_EXCEPTIONAL_RESIDUES:
                continue
            if result.outcome(q) != Outcome.WIN:
                continue
            for first in transformed_moves(q):
                if result.outcome(first) != Outcome.WIN:
                    continue
                for second in transformed_moves(first):
                    if result.outcome(second) == Outcome.WIN:
                        self.assertEqual(second, transformed_B(transformed_A(q)))

    def test_height_one_A_child_forces_loss(self) -> None:
        result = bounded_retrograde(10000)
        for q in range(1, 1000):
            child_a, child_b = transformed_moves(q)
            if transformed_B(child_a) == 0:
                self.assertEqual(transformed_B(child_b), 0)
                self.assertEqual(result.outcome(q), Outcome.LOSS)

    def test_no_certified_finite_draw_kernel_at_small_cutoff(self) -> None:
        result = bounded_retrograde(10000)
        self.assertEqual(list(certified_finite_draw_kernel(result)), [])


if __name__ == "__main__":
    unittest.main()
