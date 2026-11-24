import importlib.util
from contextlib import redirect_stdout
from io import StringIO
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/proofs/measure-private-claim-source-replay.py"
SPEC = importlib.util.spec_from_file_location("private_claim_replay_measurement", SCRIPT)
MEASURE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MEASURE)


class SourceReplayFailureTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        (self.root / "build/experiments").mkdir(parents=True)
        self.pin = self.root / "model.sha256"
        self.pin.write_text("a" * 64 + "\n", encoding="ascii")

    def assert_failure_has_no_success_record(self, reports, replay_error=None):
        output = StringIO()
        with (
            patch.object(MEASURE, "ROOT", self.root),
            patch.object(MEASURE, "MODEL_PIN", self.pin),
            patch.object(MEASURE, "run_bytes", return_value=(b"", 0.01)),
            patch.object(MEASURE, "source_report", side_effect=reports),
            patch.object(MEASURE, "files_equal", return_value=True),
            patch.object(MEASURE, "data_only_replay", side_effect=replay_error),
            redirect_stdout(output),
        ):
            with self.assertRaises((ValueError, RuntimeError)):
                MEASURE.main()
        self.assertEqual(output.getvalue(), "")

    def test_source_report_returns_command_elapsed_time(self):
        output = self.root / "report"
        report = {
            "operation": MEASURE.OPERATION,
            "status": "source-functional-and-scoped-privacy-checked",
        }
        report_bytes = json.dumps(report).encode()

        def report_command(*_args, **_kwargs):
            for name in ("audit.json", "trusted-model.ndjson", "proofs.ndjson"):
                (output / name).write_text("{}", encoding="utf-8")
            return report_bytes, 7.25

        with patch.object(MEASURE, "run_bytes", side_effect=report_command):
            result = MEASURE.source_report(output)
        self.assertEqual(result, (report_bytes, report, 7.25))

    def test_different_source_reports_emit_no_success_record(self):
        self.assert_failure_has_no_success_record([
            (b"first report", {"status": "passed"}, 1.0),
            (b"changed report", {"status": "passed"}, 1.0),
        ])

    def test_unsuccessful_data_only_replay_emits_no_success_record(self):
        self.assert_failure_has_no_success_record(
            [(b"same report", {"status": "source-functional-and-scoped-privacy-checked"}, 1.0)] * 2,
            RuntimeError("proof replay rejected"),
        )


if __name__ == "__main__":
    unittest.main()
