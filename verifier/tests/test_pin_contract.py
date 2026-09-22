"""The contract pin: every protected file is listed, checked and identified; verify.py fails closed."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

VERIFIER = Path(__file__).resolve().parents[1]
ROOT = VERIFIER.parent
sys.path.insert(0, str(VERIFIER))
import pin_contract


def run(*args, root):
    return subprocess.run([sys.executable, str(VERIFIER / "pin_contract.py"), *args, "--root", str(root)],
                          capture_output=True, text=True)


class PinContractTests(unittest.TestCase):
    def setUp(self):
        self.cfg = json.loads((ROOT / "challenges.json").read_text())
        self.pin = ROOT / self.cfg["contract"]["pin_file"]

    def test_checkout_matches_its_pin(self):
        self.assertEqual(pin_contract.mismatches(ROOT), [])
        proc = run("check", root=ROOT)
        self.assertEqual(proc.returncode, 0, proc.stderr)
        self.assertIn(self.cfg["contract"]["version"], proc.stdout)
        self.assertEqual(run("id", root=ROOT).stdout.strip(), hashlib.sha256(self.pin.read_bytes()).hexdigest())
        self.assertEqual(pin_contract.contract_id(ROOT), hashlib.sha256(self.pin.read_bytes()).hexdigest())

    def test_pin_lists_exactly_the_protected_files_sorted(self):
        listed = [line.split("  ", 1)[1] for line in self.pin.read_text().splitlines() if line.strip()]
        self.assertEqual(listed, sorted(self.cfg["protected"]))
        for line in self.pin.read_text().splitlines():
            digest, rel = line.split("  ", 1)
            self.assertEqual(digest, hashlib.sha256((ROOT / rel).read_bytes()).hexdigest(), rel)

    def copy_checkout(self, base):
        for rel in self.cfg["protected"] + [self.cfg["contract"]["pin_file"]]:
            (base / rel).parent.mkdir(parents=True, exist_ok=True)
            (base / rel).write_bytes((ROOT / rel).read_bytes())

    def test_tamper_missing_and_extra_files_fail_check(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            self.copy_checkout(base)
            self.assertEqual(run("check", root=base).returncode, 0)
            (base / "formal/LeanSphincs/Benchmark/Claim.lean").write_text("-- weakened\n")
            proc = run("check", root=base)
            self.assertEqual(proc.returncode, 1)
            self.assertIn("Claim.lean", proc.stderr)
            (base / "formal/LeanSphincs/Benchmark/Claim.lean").unlink()
            self.assertEqual(run("check", root=base).returncode, 2)
            self.copy_checkout(base)
            cfg = dict(self.cfg, protected=self.cfg["protected"] + ["verifier/extra.py"])
            (base / "verifier/extra.py").write_text("print()\n")
            (base / "challenges.json").write_text(json.dumps(cfg))
            proc = run("check", root=base)
            self.assertEqual(proc.returncode, 1)
            self.assertIn("challenges.json", proc.stderr)
            self.assertIn("extra.py", proc.stderr)
            proc = run("pin", root=base)
            self.assertEqual(proc.returncode, 0, proc.stderr)
            self.assertEqual(run("check", root=base).returncode, 0)
            self.assertNotEqual(pin_contract.contract_id(base), pin_contract.contract_id(ROOT))

    def test_missing_pin_is_an_error_not_a_pass(self):
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            self.copy_checkout(base)
            (base / self.cfg["contract"]["pin_file"]).unlink()
            self.assertEqual(run("check", root=base).returncode, 2)
            self.assertEqual(run("id", root=base).returncode, 2)


if __name__ == "__main__":
    unittest.main()
