"""Offline checks for privacy and publication boundaries of the draft uploader."""

import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("stage_drafts.py")
spec = importlib.util.spec_from_file_location("stage_drafts", SCRIPT)
stage = importlib.util.module_from_spec(spec)
spec.loader.exec_module(stage)


def packet():
    return {
        "proposal": {"name": "Offline boundary fixture", "mission_type": "ResearchPaper",
                     "description": "A local test fixture, never uploaded.", "env": stage.PIN},
        "items": [{"key": "goal", "kind": "theorem", "theorem_name": "Boundary.goal",
                   "theorem_title": "Boundary fixture", "preamble": "import Mathlib",
                   "formal_statement": "namespace Boundary\ntheorem goal : True := by sorry\nend Boundary",
                   "natural_language_statement": "The proposition true holds.", "source": "Local fixture",
                   "readback": "The proposition true holds.", "readback_model": "fixture"}],
        "main_key": "goal", "milestones": [],
    }


class StagingBoundaries(unittest.TestCase):
    def test_dry_run_does_not_need_credentials_or_network(self):
        with tempfile.TemporaryDirectory(prefix="friedmann-draft-test-") as directory:
            source = Path(directory) / "packet.json"
            source.write_text(json.dumps(packet()))
            result = subprocess.run([sys.executable, str(SCRIPT), str(source), "--credentials",
                                     str(Path(directory) / "does-not-exist.json")],
                                    stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertIn("no credentials read", result.stdout)
            self.assertEqual(list(Path(directory).iterdir()), [source])

    def test_endpoint_allowlist_excludes_publication_and_confirmation(self):
        api = object.__new__(stage.API)
        for method, endpoint in [("POST", "/submit-definition"), ("POST", "/submit-problem"),
                                 ("POST", "/verify"), ("POST", "/mission-proposals/id/submit"),
                                 ("POST", "/mission-proposals/id/items/item/confirm"),
                                 ("POST", "/missions/id/make-public"),
                                 ("POST", "/me/licensing")]:
            with self.subTest(endpoint=endpoint), self.assertRaises(stage.PacketError):
                api.request(method, endpoint, {})

    def test_definition_placeholders_and_goal_milestones_are_refused(self):
        candidate = packet()
        candidate["items"].insert(0, {"key": "def", "kind": "definition", "definition_name": "bad",
                                      "definition_title": "Bad", "definition": "axiom bad : False",
                                      "source": "Fixture", "readback": "False is assumed.",
                                      "readback_model": "fixture"})
        with self.assertRaises(stage.PacketError):
            stage.validate(candidate)
        candidate = packet()
        candidate["milestones"] = [{"key": "goal", "milestone_title": "Duplicate goal",
                                     "milestone_description": "The same theorem again."}]
        with self.assertRaises(stage.PacketError):
            stage.validate(candidate)

    def test_missing_blind_readback_is_refused(self):
        candidate = copy.deepcopy(packet())
        candidate["items"][0].pop("readback")
        with self.assertRaises(stage.PacketError):
            stage.validate(candidate)


if __name__ == "__main__":
    unittest.main()
