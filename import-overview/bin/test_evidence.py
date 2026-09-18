"""Focused checks for report extraction; no IDE, Gradle, or collector required."""

import copy
import json
import unittest
from unittest.mock import Mock

from prepare_evidence import read_report


class ReportExtractionTest(unittest.TestCase):
    def setUp(self):
        self.report = {
            "scenarios": [{
                "definition": {"name": "scenario"},
                "samples": [{"name": "elapsed", "unit": "ms"}],
                "iterations": [{"phase": "MEASURE", "values": {"elapsed": 12.5}}],
            }],
        }

    def parse(self, value):
        path = Mock()
        path.read_text.return_value = "<script>const benchmarkResult = " + json.dumps(value) + "; render();</script>"
        return read_report(path)

    def test_extracts_only_embedded_json(self):
        self.assertEqual(self.report, self.parse(self.report))

    def test_preserves_empty_failed_scenario(self):
        self.report["scenarios"][0]["iterations"] = []
        self.assertEqual([], self.parse(self.report)["scenarios"][0]["iterations"])

    def test_rejects_missing_declaration(self):
        path = Mock()
        path.read_text.return_value = "No benchmark data"
        with self.assertRaisesRegex(ValueError, "Missing benchmarkResult"):
            read_report(path)

    def test_rejects_duplicate_scenarios(self):
        self.report["scenarios"].append(copy.deepcopy(self.report["scenarios"][0]))
        with self.assertRaisesRegex(ValueError, "Duplicate scenario"):
            self.parse(self.report)

    def test_rejects_unexpected_unit(self):
        self.report["scenarios"][0]["samples"][0]["unit"] = "s"
        with self.assertRaisesRegex(ValueError, "Unexpected unit"):
            self.parse(self.report)

    def test_rejects_missing_metric(self):
        self.report["scenarios"][0]["iterations"][0]["values"] = {}
        with self.assertRaisesRegex(ValueError, "Missing metric"):
            self.parse(self.report)

    def test_rejects_invalid_durations(self):
        for value in (-1, float("nan"), float("inf"), "12"):
            with self.subTest(value=value):
                self.report["scenarios"][0]["iterations"][0]["values"]["elapsed"] = value
                with self.assertRaisesRegex(ValueError, "Invalid duration"):
                    self.parse(self.report)

    def test_rejects_unknown_iteration_phase(self):
        self.report["scenarios"][0]["iterations"][0]["phase"] = "UNKNOWN"
        with self.assertRaisesRegex(ValueError, "Unexpected iteration phase"):
            self.parse(self.report)


if __name__ == "__main__":
    unittest.main()