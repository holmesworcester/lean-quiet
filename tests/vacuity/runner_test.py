"""Regression controls for actual native-run failure modes."""
from pathlib import Path
import sys
import tempfile
import unittest
from runtime import run_checked


class NativeRunnerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.log = self.directory / 'run.log'

    def run_code(self, code, **kwargs):
        return run_checked([sys.executable, '-c', code], self.directory, self.log, **kwargs)

    def test_clean_success(self):
        self.assertEqual(self.run_code('print("1 passed")'), '1 passed\n')

    def test_zero_exit_panic_fails_on_both_streams(self):
        for stream in ['stdout', 'stderr']:
            with self.subTest(stream=stream), self.assertRaises(RuntimeError):
                self.run_code(f'import sys; print("PANIC at outOfBounds", file=sys.{stream})')
            self.assertIn('PANIC', self.log.read_text())

    def test_nonzero_exit_fails_and_retains_output(self):
        with self.assertRaises(RuntimeError):
            self.run_code('print("failed assertion"); raise SystemExit(1)')
        self.assertIn('failed assertion', self.log.read_text())

    def test_timeout_fails_and_retains_output(self):
        with self.assertRaises(RuntimeError):
            self.run_code('import time; print("before hang", flush=True); time.sleep(10)', timeout=0.5)
        self.assertIn('before hang', self.log.read_text())
        self.assertIn('TIMEOUT', self.log.read_text())


if __name__ == '__main__':
    unittest.main()
