"""Regression tests for source-integrity gates and verification dispatch."""

import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))
from projects import safe_path
from verify import code_only, static_check, verify


class VerificationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.package = Path(self.temp.name) / "example"
        self.package.mkdir()
        self.write("Main.lean", "import Helper\ntheorem main : True := by trivial\n")
        self.write("Helper.lean", "theorem helper : True := by trivial\n")
        self.write("proof/Audit.lean", "import Main\n#check main\n")
        self.write("lakefile.toml", 'name = "example"\ndefaultTargets = ["Main"]\n[[lean_lib]]\nname = "Main"\n')
        self.write("lean-toolchain", "leanprover/lean4:v4.19.0\n")
        self.write("lake-manifest.json", json.dumps({"packages": [{"name": "mathlib", "type": "git", "rev": "a"*40}]}))
        self.meta = {"schema_version": 1, "name": "example", "lake_project": ".",
                     "lean_toolchain": "leanprover/lean4:v4.19.0",
                     "source_files": {name: self.sha(name) for name in ["Main.lean", "Helper.lean", "proof/Audit.lean"]},
                     "config_files": {name: self.sha(name) for name in ["lakefile.toml", "lean-toolchain", "lake-manifest.json"]},
                     "production_files": ["Main.lean", "Helper.lean"], "audit_files": ["proof/Audit.lean"]}
        self.save()

    def write(self, relative, text):
        path = self.package / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def sha(self, relative):
        return hashlib.sha256((self.package/relative).read_bytes()).hexdigest()

    def save(self):
        self.write("project.json", json.dumps(self.meta))

    def test_valid_source_inventory(self):
        self.assertEqual(set(static_check(self.package)[3]), {"Main", "Helper"})

    def test_rejects_missing_added_and_changed_sources(self):
        for mutation in ["missing", "added", "changed"]:
            with self.subTest(mutation=mutation):
                original = (self.package/"Helper.lean").read_bytes()
                if mutation == "missing":
                    (self.package/"Helper.lean").unlink()
                elif mutation == "added":
                    self.write("Extra.lean", "theorem extra : True := by trivial\n")
                else:
                    self.write("Helper.lean", "theorem helper : False := by sorry\n")
                with self.assertRaises(ValueError):
                    static_check(self.package)
                (self.package/"Helper.lean").write_bytes(original)
                (self.package/"Extra.lean").unlink(missing_ok=True)

    def test_rejects_trust_escape_even_with_updated_fingerprint(self):
        self.write("Helper.lean", "theorem helper : False := by sorry\n")
        self.meta["source_files"]["Helper.lean"] = self.sha("Helper.lean")
        self.save()
        with self.assertRaisesRegex(ValueError, "Trust escape"):
            static_check(self.package)

    def test_nested_comments_strings_and_character_quotes(self):
        source = '/- sorry /- admit -/ -/\n-- axiom\ndef text := "sorry\\\"admit"\ndef quote := \'"\'\ntheorem ok : True := by trivial\n'
        clean = code_only(source)
        self.assertEqual(clean.count("\n"), source.count("\n"))
        self.assertNotIn("sorry", clean)
        self.assertIn("theorem ok", clean)
        with self.assertRaisesRegex(ValueError, "Unterminated"):
            code_only("/- not closed")

    def test_rejects_path_traversal(self):
        for path in ["../outside", "C:/outside", "/outside", "a\\b"]:
            with self.subTest(path=path), self.assertRaises(ValueError):
                safe_path(self.package, path)

    def test_rejects_unpinned_dependencies(self):
        self.write("lake-manifest.json", json.dumps({"packages": [{"name": "mathlib", "type": "path", "dir": "../cache"}]}))
        self.meta["config_files"]["lake-manifest.json"] = self.sha("lake-manifest.json")
        self.save()
        with self.assertRaisesRegex(ValueError, "not locked"):
            static_check(self.package)

    def test_rejects_unclassified_source(self):
        self.meta["production_files"].remove("Helper.lean")
        self.save()
        with self.assertRaisesRegex(ValueError, "Every Lean file"):
            static_check(self.package)

    def test_audit_runtime_data_must_be_fingerprinted(self):
        self.write("proof/Audit.lean", 'import Main\n#eval IO.FS.readFile "proof/declarations.json"\n')
        self.meta["source_files"]["proof/Audit.lean"] = self.sha("proof/Audit.lean")
        self.write("proof/declarations.json", "[]\n")
        self.save()
        with self.assertRaisesRegex(ValueError, "Audit input is not fingerprinted"):
            static_check(self.package)
        self.meta["config_files"]["proof/declarations.json"] = self.sha("proof/declarations.json")
        self.save()
        static_check(self.package)

    def test_static_does_not_replace_full_verification(self):
        self.write("proof/verification.json", '{"status":"earlier"}')
        result = verify(self.package, static=True)
        self.assertEqual(result["status"], "passed")
        self.assertFalse(result["manuscript_coverage_certified"])
        self.assertEqual(json.loads((self.package/"proof/verification.json").read_text())["status"], "earlier")

    def test_full_verification_compiles_every_module_and_runs_audit(self):
        commands = []
        def record(command, cwd, logfile, timeout):
            commands.append(command)
            return {"exit_code": 0}
        with patch("verify.shutil.which", return_value="lake"), \
             patch("verify.subprocess.check_output", return_value="Lean (version 4.19.0, x86_64)"), \
             patch("verify.run_logged", side_effect=record):
            result = verify(self.package)
        self.assertEqual(result["status"], "passed")
        self.assertEqual(commands[0], ["lake", "build", "Main"])
        self.assertEqual(commands[1], ["lake", "build", "+Helper", "+Main"])
        self.assertIn(str((self.package/"proof/Audit.lean").resolve()), commands[-1])

    def test_failed_full_verification_replaces_stale_success(self):
        self.write("proof/verification.json", '{"status":"passed"}')
        with patch("verify.shutil.which", return_value=None), self.assertRaises(ValueError):
            verify(self.package)
        result = json.loads((self.package/"proof/verification.json").read_text())
        self.assertEqual(result["status"], "failed")
        self.assertIn("lake is not on PATH", result["error"])

    def test_wrong_lean_version_is_rejected_before_build(self):
        with patch("verify.shutil.which", return_value="lake"), \
             patch("verify.subprocess.check_output", return_value="Lean (version 4.20.0, x86_64)"), \
             patch("verify.run_logged") as command, self.assertRaisesRegex(ValueError, "Unexpected active Lean"):
            verify(self.package)
        command.assert_not_called()


if __name__ == "__main__":
    unittest.main()
