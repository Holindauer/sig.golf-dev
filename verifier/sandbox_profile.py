"""Pinned Linux verifier profile. No fallback to an unsandboxed ranked run."""

import ctypes
import os
from pathlib import Path
import platform
import uuid

PROFILE = "leansphincs-linux-v1"


def landlock_abi() -> int:
    if platform.system() != "Linux" or platform.machine() not in {"x86_64", "aarch64"}:
        raise RuntimeError("verified sandbox profile requires Linux x86_64 or aarch64")
    libc = ctypes.CDLL(None, use_errno=True)
    # landlock_create_ruleset(NULL, 0, LANDLOCK_CREATE_RULESET_VERSION)
    result = libc.syscall(444, ctypes.c_void_p(), ctypes.c_size_t(0), ctypes.c_uint(1))
    if result < 8:
        raise RuntimeError(f"Landlock ABI >= 8 is required (got {result}, errno {ctypes.get_errno()})")
    return result


def systemd_command(command: list[str], cwd: Path, environment: dict[str, str],
                    runtime_seconds: int = 4800) -> list[str]:
    if not 1 <= runtime_seconds <= 4800:
        raise ValueError("invalid verifier runtime limit")
    args = ["systemd-run", "--user", "--wait", "--pipe", "--collect", "--quiet",
            f"--unit=leansphincs-{uuid.uuid4().hex}.service",
            "--property=MemoryMax=24G", "--property=MemorySwapMax=0",
            "--property=TasksMax=256", "--property=TimeoutStopSec=5", f"--property=RuntimeMaxSec={runtime_seconds}",
            "--property=LimitCORE=0", "--property=LimitFSIZE=2147483648",
            "--property=NoNewPrivileges=yes", "--property=UMask=0077",
            "--property=SystemCallFilter=~@network-io @mount @reboot @swap @raw-io @debug",
            "--property=SystemCallErrorNumber=EPERM", "--property=KillMode=control-group",
            f"--working-directory={cwd}"]
    # env -i also removes variables inherited from the systemd user manager.
    return args + ["--", "/usr/bin/env", "-i"] + [f"{k}={v}" for k, v in sorted(environment.items())] + command


def landrun_args(binary: Path, root: Path, lean: Path, exporter: Path,
                 command: list[str], build: bool = False,
                 submission_prefix: str = "LeanSphincs.Submission") -> list[str]:
    landlock_abi()
    # Pinned landrun targets ABI 9. ABI 8 lacks only its pathname UNIX-socket
    # rights, compensated by the outer mandatory @network-io seccomp denial.
    # The ABI floor and active socket probes are mandatory; no silent fallback.
    args = [str(binary), "--best-effort", "--ro", str(root), "--rox", str(lean),
            "--rox", str(exporter), "--rox", "/usr/bin/git", "--ldd", "--add-exec"]
    for library in ("/lib", "/lib64", "/usr/lib"):
        if Path(library).exists():
            args += ["--rox", library]
    args += ["--rw", "/dev/null", "--ro", "/dev/urandom"]
    for package in sorted((root / ".lake/packages").iterdir()):
        args += ["--ro", str(package.resolve())]
    for key in ("PATH", "HOME", "LEAN_PATH", "LEAN_ABORT_ON_PANIC"):
        if key in os.environ:
            args += ["--env", key]
    if build:
        for parent in ("lib/lean", "ir"):
            args += ["--rw", str(root / f".lake/build/{parent}" / submission_prefix.replace(".", "/"))]
    return args + ["--"] + command
