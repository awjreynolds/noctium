"""Check the offline verifier for the retained List.head comparison."""

import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


ROOT = Path(__file__).resolve().parents[1]
CHECKER = ROOT / "scripts/check-compact-comparison-record.py"
RECORD = ROOT / "tests/compact/list-head-comparison-v1/record.json"


def run_checker(*args):
    return subprocess.run(
        [sys.executable, str(CHECKER), *args],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )


class CompactComparisonRecordTests(unittest.TestCase):
    def test_retained_record_passes(self):
        result = run_checker()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_changed_fixture_digest_rejects(self):
        record = json.loads(RECORD.read_bytes())
        fixture = "tests/NativeScalarListMaybe.lean"
        record["inputs"][fixture] = "0" * 64

        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "changed-record.json"
            path.write_text(json.dumps(record), encoding="utf-8")
            result = run_checker("--record", str(path))

        self.assertNotEqual(result.returncode, 0)
        self.assertIn(f"input digest mismatch: {fixture}", result.stderr)


if __name__ == "__main__":
    unittest.main()
