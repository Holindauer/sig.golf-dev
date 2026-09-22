"""Capture submission bytes once; validate and compile only that private copy."""

import hashlib
import json
import os
from pathlib import Path
import re
import stat

REQUIRED = {"Scheme.lean", "Solution.lean", "sigma.txt", "hverify.txt", "bound.txt"}
MAX_FILE = 4 * 1024 * 1024
MAX_TOTAL = 10 * 1024 * 1024


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
                if len(names) > 1000:
                    raise ValueError("submission exceeds 1000 files")
        names.sort()
        if not REQUIRED.issubset(names):
            raise ValueError("missing submission artifacts: " + ", ".join(sorted(REQUIRED - set(names))))
        bundle = {}
        total = 0
        for name in names:
            if name not in REQUIRED and not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*\.lean", name):
                raise ValueError(f"{name!r}: expected a flat Lean module filename or declared metric")
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
            if name.endswith(".lean"):
                text = data.decode("utf-8", errors="strict")
                if "\x00" in text:
                    raise ValueError(f"{name}: NUL is not admitted")
            bundle[name] = data
        return bundle
    finally:
        os.close(descriptor)


def manifest(bundle: dict[str, bytes]) -> dict:
    files = {name: {"bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
             for name, data in sorted(bundle.items())}
    encoded = json.dumps(files, sort_keys=True, separators=(",", ":")).encode()
    return {"sha256": hashlib.sha256(encoded).hexdigest(), "files": files}


def materialize(bundle: dict[str, bytes], destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=False)
    for name, data in bundle.items():
        with (destination / name).open("xb") as stream:
            stream.write(data)
