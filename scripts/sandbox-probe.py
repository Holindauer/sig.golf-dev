#!/usr/bin/env python3
"""Executed *inside* the production child profile; only synthetic test data."""

import errno
import json
from pathlib import Path
import socket
import sys


def denied(action):
    try:
        action()
    except OSError as error:
        if error.errno in (errno.EACCES, errno.EPERM):
            return
        raise
    raise RuntimeError("sandbox allowed a forbidden operation")


root = Path.cwd()
outside = Path(sys.argv[1])
assert (root / "protected.txt").read_text() == "protected"
assert (root / ".lake/packages/probe/readonly.txt").read_text() == "dependency"
denied(lambda: outside.read_text())
denied(lambda: (root / "protected.txt").write_text("changed"))
denied(lambda: (root / ".lake/build/lib/lean/LeanSphincs/Benchmark/protected.olean").write_text("changed"))
denied(lambda: (root / ".lake/config/protected.olean").write_text("changed"))
denied(lambda: (root / ".lake/packages/probe/readonly.txt").write_text("changed"))
denied(lambda: (root / "LeanSphincs/Submission/Scheme.lean").write_text("changed"))
for family, kind in [(socket.AF_INET, socket.SOCK_STREAM), (socket.AF_INET, socket.SOCK_DGRAM),
                     (socket.AF_INET6, socket.SOCK_STREAM), (socket.AF_UNIX, socket.SOCK_STREAM)]:
    denied(lambda: socket.socket(family, kind))
for parent in ("lib/lean", "ir"):
    artifact = root / f".lake/build/{parent}/LeanSphincs/Submission/probe.txt"
    if sys.argv[2] == "compile":
        artifact.write_text("allowed")
    else:
        denied(lambda: artifact.write_text("substituted"))
        denied(lambda: artifact.unlink())
print(json.dumps({"probe": "passed", "checks": ["outside_read", "protected_write", "protected_cache_write", "config_write",
    "dependency_write", "source_write", "tcp", "udp", "ipv6", "unix_socket", "build_write" if sys.argv[2] == "compile" else "artifact_write_denied"]}))
