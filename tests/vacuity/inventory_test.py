"""The tracker must preserve pending entries and detect added README references."""
import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('vacuity', ROOT / 'ci/vacuity.py')
vacuity = importlib.util.module_from_spec(spec)
spec.loader.exec_module(vacuity)


class InventoryTest(unittest.TestCase):
    def setUp(self):
        self.readme = (ROOT / 'README.md').read_text().split(vacuity.BEGIN)[0]

    def test_every_reference_has_exactly_one_row(self):
        block = vacuity.report(self.readme)
        refs = vacuity.references(self.readme)
        self.assertEqual(block.count('\n| [`'), len(refs))
        self.assertEqual(block.count('Pending: no concrete'), len(refs) - len(vacuity.CHECKS))

    def test_new_reference_is_pending_and_changes_report(self):
        changed = vacuity.report(self.readme + '\n[`new_law`]: imaginary.lean#L1\n')
        self.assertNotEqual(changed, vacuity.report(self.readme))
        self.assertIn('| [`new_law`](imaginary.lean#L1) | Pending:', changed)

    def test_removed_checked_reference_fails(self):
        with self.assertRaisesRegex(ValueError, 'checked references disappeared'):
            vacuity.report(self.readme.replace('[`fit_small`]:', '[`renamed`]:'))

    def test_existing_report_is_not_counted_again(self):
        self.assertEqual(vacuity.report(self.readme), vacuity.report((ROOT / 'README.md').read_text()))


if __name__ == '__main__':
    unittest.main()
