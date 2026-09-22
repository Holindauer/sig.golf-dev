"""Exact source retention, crash-safe publication and retry; no Lean or network required."""
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import zipfile

VERIFIER = Path(__file__).resolve().parents[1]
ROOT = VERIFIER.parent
sys.path.insert(0, str(VERIFIER))
import source_archive as archive


class SourceArchiveTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="sig-archive-test-")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.sub = self.root / "input"
        self.sub.mkdir()
        (self.sub / "Scheme.lean").write_bytes(b"-- scheme\n")
        (self.sub / "Solution.lean").write_bytes(b"-- exact source\r\n")
        (self.sub / "sigma.txt").write_bytes(b"2274\n")
        (self.sub / "hverify.txt").write_bytes(b"160\n")
        (self.sub / "bound.txt").write_bytes(b"[[4,1,1,0,128]]\n")
        (self.sub / "NOTES.md").write_bytes(b"a note\n")
        self.store = self.root / "sources"
        self.sid = "1" * 32
        self.identity = dict(source_repo="https://github.com/author/proofs.git", commit="a" * 40,
                             track="full", submission_root="formal/Submissions/Full", contract="b" * 64)

    def save(self, sid=None):
        return archive.save_source(self.store, sid or self.sid, self.sub, **self.identity)

    def test_limits_mirror_the_contract(self):
        limits = json.loads((ROOT / "challenges.json").read_text())["limits"]
        self.assertEqual((archive.MAX_FILES, archive.MAX_FILE_BYTES, archive.MAX_TOTAL_BYTES),
                         (limits["max_files"], limits["max_file_bytes"], limits["max_total_bytes"]))

    def test_exact_deterministic_archive_and_safe_layout(self):
        first = self.save()
        second = self.save("2" * 32)
        self.assertEqual(first, second)
        self.assertEqual(archive.read_metadata(self.store, self.sid), first)
        path = archive.validated_path(self.store, first)
        self.assertEqual(hashlib.sha256(path.read_bytes()).hexdigest(), first["sha256"])
        with zipfile.ZipFile(path) as z:
            self.assertEqual(z.read(self.identity["submission_root"] + "/Solution.lean"), b"-- exact source\r\n")
            self.assertEqual(z.read(self.identity["submission_root"] + "/NOTES.md"), b"a note\n")
            self.assertEqual(len(z.infolist()), 7)
            self.assertIn(archive.MANIFEST, z.namelist())
            self.assertTrue(all(i.compress_type == zipfile.ZIP_STORED for i in z.infolist()))
        self.assertEqual(first["file_count"], 6)

    def test_historical_bytes_survive_source_change_or_removal(self):
        meta = self.save()
        original = archive.validated_path(self.store, meta).read_bytes()
        (self.sub / "Solution.lean").write_text("-- newer head\n")
        with self.assertRaises(archive.ArchiveError):
            self.save()
        shutil.rmtree(self.sub)
        self.assertEqual(archive.validated_path(self.store, meta).read_bytes(), original)
        restored = self.root / "retry"
        archive.restore_source(self.store, meta, restored, **{k: self.identity[k] for k in
            ("commit", "track", "contract", "submission_root")})
        self.assertEqual((restored / "Solution.lean").read_bytes(), b"-- exact source\r\n")
        self.assertEqual(sorted(p.name for p in restored.iterdir()),
                         ["NOTES.md", "Scheme.lean", "Solution.lean", "bound.txt", "hverify.txt", "sigma.txt"])

    def test_retry_refuses_wrong_commit_track_or_contract(self):
        meta = self.save()
        for key, value in (("commit", "c" * 40), ("track", "other"), ("contract", "d" * 64),
                           ("submission_root", "formal/Submissions/Other")):
            expected = {k: self.identity[k] for k in ("commit", "track", "contract", "submission_root")}
            expected[key] = value
            with self.subTest(key=key), self.assertRaises(archive.ArchiveError):
                archive.restore_source(self.store, meta, self.root / "retry", **expected)
        self.assertFalse((self.root / "retry").exists())

    def test_corruption_and_symlinks_are_never_served(self):
        meta = self.save()
        path = archive.object_path(self.store, meta)
        path.write_bytes(b"corrupt")
        with self.assertRaises(archive.ArchiveError):
            archive.validated_path(self.store, meta)
        path.unlink()
        path.symlink_to(self.sub / "Solution.lean")
        with self.assertRaises(OSError):
            archive.validated_path(self.store, meta)

    def test_rejects_unsafe_names_and_metadata(self):
        for key, value in (("sha256", "../outside"), ("size_bytes", True),
                           ("submission_root", "../elsewhere"), ("submission_root", "submissions/full"),
                           ("commit", "main")):
            meta = self.save()
            meta[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(archive.ArchiveError):
                archive.validate_metadata(meta)
        with self.assertRaises(archive.ArchiveError):
            archive.read_metadata(self.store, "../outside")
        (self.sub / "Extra.lean").symlink_to(self.sub / "Solution.lean")
        with self.assertRaises(OSError):
            self.save("3" * 32)
        (self.sub / "Extra.lean").unlink()
        (self.sub / "OTHER.md").write_bytes(b"x")
        with self.assertRaises(archive.ArchiveError):
            self.save("4" * 32)

    def test_missing_archive_and_missing_index_are_distinct(self):
        self.assertIsNone(archive.read_metadata(self.store, self.sid))
        meta = self.save()
        archive.object_path(self.store, meta).unlink()
        self.assertEqual(archive.read_metadata(self.store, self.sid), meta)
        with self.assertRaises(OSError):
            archive.validated_path(self.store, meta)

    def test_no_partial_index_on_publication_failure(self):
        original = archive._publish
        def fail_sidecar(path, data):
            if path.suffix == ".json":
                raise OSError("simulated interrupted sidecar publication")
            return original(path, data)
        with patch.object(archive, "_publish", side_effect=fail_sidecar), self.assertRaises(OSError):
            self.save()
        self.assertIsNone(archive.read_metadata(self.store, self.sid))
        self.assertEqual(len(list(self.store.glob("*.zip"))), 1)
        meta = self.save()
        self.assertEqual(archive.read_metadata(self.store, self.sid), meta)
        self.assertEqual(list(self.store.glob(".archive-*")), [])

    def test_low_disk_space_preserves_room_for_failure_record(self):
        with patch.object(archive.shutil, "disk_usage", return_value=SimpleNamespace(free=1)), \
                self.assertRaises(archive.ArchiveError):
            self.save()
        self.assertEqual(list(self.store.iterdir()), [])


if __name__ == "__main__":
    unittest.main()
