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


class OrderingTest(unittest.TestCase):
    def setUp(self):
        # Definitions deliberately disagree with table order; assumptions and
        # prose cite later declarations before the theorem tables do.
        self.source = '''## What is proven
[`assumption`] and [`quality`] appear in prose first.
### What is Assumed
[`assumption`]
### Security proofs
| | | Guarantee | Theorems |
|---|---|---|---|
| | | **Identity and membership** | |
| yes | high | First guarantee mentions [`support`]. | [`first`], [`second`] |
| yes | high | Repeated support. | [`second`], [`third`] |
### Quality proofs
| | | Guarantee | Theorems |
|---|---|---|---|
| yes | high | Quality promise. | [`quality`], [`first`] |
### Not yet about running code (todo)
| model | [`support`] |
[`assumption`]: assumptions.lean#L1
[`quality`]: quality.lean#L1
[`support`]: support.lean#L1
[`third`]: third.lean#L1
[`first`]: first.lean#L1
[`second`]: second.lean#L1
'''

    def test_table_order_precedes_prose_and_definitions(self):
        self.assertEqual(list(vacuity.ordered_references(self.source)),
                         ['first', 'second', 'third', 'quality', 'assumption', 'support'])

    def test_reordering_guarantees_changes_inventory_order(self):
        changed = self.source.replace('[`first`], [`second`]', '[`third`], [`first`]')
        self.assertEqual(list(vacuity.ordered_references(changed))[:4],
                         ['third', 'first', 'second', 'quality'])

    def test_repeated_declarations_have_one_entry_and_keep_targets(self):
        ordered = vacuity.ordered_references(self.source)
        self.assertEqual(len(ordered), len(vacuity.references(self.source)))
        self.assertEqual(ordered['first'], 'first.lean#L1')

    def test_unlisted_declarations_remain_at_end(self):
        changed = self.source + '[`new_support`]: support.lean#L2\n'
        self.assertEqual(list(vacuity.ordered_references(changed))[-1], 'new_support')

    def test_generated_report_cannot_reorder_or_add_entries(self):
        changed = self.source + vacuity.BEGIN + '\n### Security proofs\n| [`invented`] |\n'
        self.assertEqual(vacuity.ordered_references(changed),
                         vacuity.ordered_references(self.source))

    def test_undefined_table_reference_fails(self):
        changed = self.source.replace('[`first`], [`second`]', '[`undefined`]')
        with self.assertRaisesRegex(ValueError, 'proof table reference has no definition: undefined'):
            vacuity.ordered_references(changed)

    def test_readme_begins_with_identity_membership_theorems(self):
        source = (ROOT / 'README.md').read_text()
        expected = ['no_impersonation', 'admission_needs_approval', 'admission_approved',
                    'request_invited', 'removal_authorized', 'admin_granted',
                    'removed_stays', 'valid_stays']
        self.assertEqual(list(vacuity.ordered_references(source))[:len(expected)], expected)


if __name__ == '__main__':
    unittest.main()
