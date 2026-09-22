"""Capture submission bytes once; validate and compile only that private copy."""

import hashlib
import json
import os
from pathlib import Path
import re
import stat

REQUIRED = {"Scheme.lean", "Solution.lean", "sigma.txt", "hverify.txt", "bound.txt"}
# Optional notes for the next solver and a root README. Both are captured and bound by the
# receipt and published by the site; neither enters the Lean project or the comparator.
OPTIONAL_DOCS = {"NOTES.md", "README.md"}
LEAN_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*\.lean")
MAX_FILE = 4 * 1024 * 1024
MAX_TOTAL = 10 * 1024 * 1024
MAX_FILES = 1000


def capture(root: Path) -> dict[str, bytes]:
    """Use directory-relative, no-follow opens; never follow a swapped symlink.

    The resulting bytes, not a claim about simultaneous state of a live folder,
    are the submission. Size limits apply to actual reads as well as metadata.
    """
    descriptor = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        names = []
        with os.scandir(descriptor) as entries:
            for entry in entries:
                names.append(entry.name)
                if len(names) > MAX_FILES:
                    raise ValueError(f"submission exceeds {MAX_FILES} files")
        names.sort()
        if not REQUIRED.issubset(names):
            raise ValueError("missing submission artifacts: " + ", ".join(sorted(REQUIRED - set(names))))
        bundle = {}
        total = 0
        for name in names:
            if name not in REQUIRED and name not in OPTIONAL_DOCS and not LEAN_NAME.fullmatch(name):
                raise ValueError(f"{name!r}: expected a flat Lean module filename, a declared metric, "
                                 "NOTES.md or README.md")
            fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_NONBLOCK, dir_fd=descriptor)
            with os.fdopen(fd, "rb") as stream:
                info = os.fstat(stream.fileno())
                if not stat.S_ISREG(info.st_mode):
                    raise ValueError(f"{name}: only regular files are admitted")
                if info.st_size > MAX_FILE:
                    raise ValueError(f"{name}: exceeds 4 MiB")
                data = stream.read(MAX_FILE + 1)
                if len(data) > MAX_FILE:
                    raise ValueError(f"{name}: exceeds 4 MiB")
            total += len(data)
            if total > MAX_TOTAL:
                raise ValueError("submission exceeds 10 MiB total")
            if name.endswith(".lean") or name in OPTIONAL_DOCS:
                text = data.decode("utf-8", errors="strict")
                if "\x00" in text:
                    raise ValueError(f"{name}: NUL is not admitted")
            bundle[name] = data
        return bundle
    finally:
        os.close(descriptor)


def lean_sources(bundle: dict[str, bytes]) -> dict[str, bytes]:
    """The part of a bundle that enters the Lean project: everything except the optional docs."""
    return {name: data for name, data in bundle.items() if name not in OPTIONAL_DOCS}


def manifest_of_files(files: dict) -> dict:
    files = {name: files[name] for name in sorted(files)}
    encoded = json.dumps(files, sort_keys=True, separators=(",", ":")).encode()
    return {"sha256": hashlib.sha256(encoded).hexdigest(), "files": files}


def manifest(bundle: dict[str, bytes]) -> dict:
    return manifest_of_files({name: {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
                              for name, data in bundle.items()})


def without_docs(captured: dict) -> dict:
    """The manifest a Lean-project recapture must reproduce: the captured manifest minus the docs."""
    return manifest_of_files({name: entry for name, entry in captured["files"].items()
                              if name not in OPTIONAL_DOCS})


def materialize(bundle: dict[str, bytes], destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=False)
    for name, data in bundle.items():
        with (destination / name).open("xb") as stream:
            stream.write(data)
