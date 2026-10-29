"""The pixel gate must reject drift, missing cases and mismatched viewports."""
import tempfile
from pathlib import Path
import unittest

from PIL import Image, ImageDraw
from compare import compare, metrics


class PixelGate(unittest.TestCase):
    def test_sidebar_shift_and_border_are_visible_to_the_gate(self):
        reference = Image.new('RGB', (390, 200), 'white')
        ImageDraw.Draw(reference).rectangle((0, 0, 99, 199), fill='#7647c7')
        moved = Image.new('RGB', reference.size, 'white')
        ImageDraw.Draw(moved).rectangle((0, 0, 119, 199), fill='#7647c7')
        identical, _ = metrics(reference, reference)
        shifted, _ = metrics(reference, moved)
        self.assertEqual(identical['mae'], 0)
        self.assertGreater(shifted['layout_mae'], .01)
        border = reference.copy()
        ImageDraw.Draw(border).line((100, 0, 100, 199), fill='black', width=1)
        self.assertGreater(metrics(reference, border)[0]['mae'], 0)

    def test_missing_or_changed_frame_cannot_pass_or_update_the_reference(self):
        with tempfile.TemporaryDirectory() as d:
            root = Path(d)
            ref, actual, out = (root / n for n in ['reference', 'actual', 'report'])
            ref.mkdir(); actual.mkdir()
            Image.new('RGB', (32, 32), 'white').save(ref / 'home.png')
            before = (ref / 'home.png').read_bytes()
            budgets = {'home': {'mae': 0}}
            self.assertTrue(compare(ref, actual, out, budgets)[1])
            Image.new('RGB', (32, 32), 'black').save(actual / 'home.ppm')
            self.assertTrue(compare(ref, actual, out, budgets)[1])
            self.assertEqual((ref / 'home.png').read_bytes(), before)
            self.assertTrue((out / 'home-diff.png').is_file())
            self.assertTrue((out / 'index.html').is_file())

    def test_viewport_mismatch_is_not_hidden_by_resizing(self):
        with self.assertRaises(ValueError):
            metrics(Image.new('RGB', (390, 844)), Image.new('RGB', (400, 844)))


if __name__ == '__main__':
    unittest.main()
