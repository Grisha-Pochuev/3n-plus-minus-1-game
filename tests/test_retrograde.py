import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "src"))

from optimal_3n1.game import transformed_moves  # noqa: E402
from optimal_3n1.retrograde import Outcome, bounded_retrograde  # noqa: E402


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


if __name__ == "__main__":
    unittest.main()
