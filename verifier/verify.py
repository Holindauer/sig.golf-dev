#!/usr/bin/env python3
"""Check one frozen beta PR using a trusted challenge and an isolated comparator.

Local mode is for development only. Linux refuses to compile untrusted code without the
systemd + Landlock sandbox; the checker is never given the GitHub token.
"""
from __future__ import annotations

import argparse
import ctypes
import json
import os
import platform
import re
import selectors
import shutil
import signal
import subprocess
import sys
import tempfile
import time
import uuid
from pathlib import Path

from check_submission import check
from fetch import FetchError, fetch_pr

HERE = Path(__file__).resolve().parent
TRUSTED = HERE.parent
LOG_CAP = 4 * 1024 * 1024
WALL_SECONDS = 4 * 3600
MEMORY_BYTES = 24 * 1024**3


class VerifyError(ValueError):
    pass


def tools_env(root: Path) -> dict[str, str]:
    path = root / 'verifier' / '.tools' / 'env.sh'
    if not path.is_file():
        raise VerifyError('verification tools missing; run verifier/setup_tools.sh')
    values = {}
    for line in path.read_text().splitlines():
        if line.startswith('export ') and '=' in line:
            name, value = line[7:].split('=', 1)
            values[name] = value.strip().strip('"')
    for name in ('COMPARATOR_BIN', 'COMPARATOR_LEAN4EXPORT', 'COMPARATOR_LANDRUN'):
        file = Path(values.get(name, ''))
        if not file.is_absolute() or not file.is_file() or not os.access(file, os.X_OK):
            raise VerifyError(f'{name} must point to an installed executable')
    return values


def clone_tree(src: Path, dst: Path) -> None:
    if platform.system() == 'Darwin':
        cmd = ['cp', '-c', '-R', str(src), str(dst)]
    else:
        cmd = ['cp', '-a', '--reflink=auto', str(src), str(dst)]
    subprocess.run(cmd, check=True, timeout=600, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE)


def linux_preflight(env: dict[str, str]) -> None:
    if os.geteuid() == 0:
        raise VerifyError('refusing to compile candidate code as root')
    if not shutil.which('systemd-run') or not shutil.which('systemctl'):
        raise VerifyError('systemd user services are required on Linux')
    lsm = Path('/sys/kernel/security/lsm')
    if not lsm.is_file() or 'landlock' not in lsm.read_text().strip().split(','):
        raise VerifyError('Landlock is not enabled')
    if Path(env['COMPARATOR_LANDRUN']).open('rb').read(4) != b'\x7fELF':
        raise VerifyError('a compiled Landrun binary is required on Linux')
    if platform.machine() not in {'x86_64', 'aarch64', 'riscv64'}:
        raise VerifyError('unsupported Linux architecture')
    libc = ctypes.CDLL(None, use_errno=True)
    libc.syscall.restype = ctypes.c_long
    abi = int(libc.syscall(ctypes.c_long(444), ctypes.c_void_p(), ctypes.c_size_t(0), ctypes.c_uint(1)))
    if abi < 3:
        raise VerifyError('Landlock ABI 3 or newer is required')


def linux_command(cmd: list[str], project: Path, env: dict[str, str], hidden: list[Path]) -> tuple[list[str], dict[str, str]]:
    unit = 'sig-verify-' + uuid.uuid4().hex[:12]
    # Lake scales its parallel builds to visible CPUs; the host has eight CPUs but the
    # verification cgroup has only 24 GiB. Keep large independent Lean modules from
    # collectively exhausting that memory limit.
    cpus = sorted(os.sched_getaffinity(0))[:2]
    properties = [f'MemoryMax={MEMORY_BYTES}', 'MemorySwapMax=0', f'RuntimeMaxSec={WALL_SECONDS}',
                  f'CPUAffinity={" ".join(map(str, cpus))}',
                  'KillMode=control-group', 'TimeoutStopSec=5', 'SendSIGKILL=yes', 'TasksMax=512',
                  'RestrictAddressFamilies=~AF_UNIX', 'NoNewPrivileges=yes', 'ProtectSystem=strict',
                  f'ReadWritePaths={project / ".lake"}', 'PrivatePIDs=yes', 'ProcSubset=pid',
                  'InaccessiblePaths=/sys',
                  'InaccessiblePaths=' + ' '.join(f'-{p}' for p in ['/etc/ots', '/etc/sig-golf', *hidden]),
                  'PrivateDevices=yes', 'TemporaryFileSystem=/dev/shm', 'PrivateIPC=yes',
                  'SystemCallErrorNumber=EPERM',
                  'SystemCallFilter=~@network-io @debug ptrace process_vm_readv process_vm_writev '
                  'pidfd_getfd kill tkill tgkill pidfd_send_signal']
    clean = {'PATH': f'{Path.home() / ".elan/bin"}:{os.environ.get("PATH", "/usr/bin:/bin")}',
             'HOME': str(Path.home()), 'LANG': 'C.UTF-8',
             'COMPARATOR_LANDRUN': env['COMPARATOR_LANDRUN'],
             'COMPARATOR_LEAN4EXPORT': env['COMPARATOR_LEAN4EXPORT'],
             'SIG_VERIFIER_HOST_DEV': str(Path('/dev').stat().st_dev),
             'SIG_VERIFIER_HOST_PIDNS': str(Path('/proc/self/ns/pid').stat().st_ino),
             'SIG_VERIFIER_HOST_SHM_DEV': str(Path('/dev/shm').stat().st_dev)}
    command = ['/usr/bin/env', '-i', *[f'{k}={v}' for k, v in clean.items()],
               sys.executable, str(HERE / 'linux_exec.py'), *cmd]
    runtime = os.environ.get('XDG_RUNTIME_DIR', f'/run/user/{os.getuid()}')
    bus_env = {'PATH': clean['PATH'], 'HOME': clean['HOME'], 'XDG_RUNTIME_DIR': runtime,
               'DBUS_SESSION_BUS_ADDRESS': os.environ.get('DBUS_SESSION_BUS_ADDRESS', f'unix:path={runtime}/bus')}
    return (['systemd-run', '--user', '--wait', '--collect', '--pipe', '--quiet', f'--unit={unit}',
             f'--working-directory={project}',
             *[arg for prop in properties for arg in ('-p', prop)], '--', *command], bus_env)


def run_checked(cmd: list[str], cwd: Path, env: dict[str, str], log: Path) -> tuple[int, bool]:
    """Capture at most 4 MiB; keep draining; kill the process group at the outer deadline."""
    proc = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            start_new_session=True, bufsize=0)
    deadline = time.monotonic() + WALL_SECONDS + 120
    truncated = False
    timed_out = False
    try:
        os.set_blocking(proc.stdout.fileno(), False)
        with selectors.DefaultSelector() as selector, log.open('wb') as output:
            selector.register(proc.stdout, selectors.EVENT_READ)
            kept = 0
            while True:
                remain = deadline - time.monotonic()
                if remain <= 0:
                    timed_out = True
                    break
                if not selector.select(remain):
                    continue
                try:
                    chunk = os.read(proc.stdout.fileno(), 65536)
                except BlockingIOError:
                    continue
                if not chunk:
                    break
                if kept < LOG_CAP:
                    output.write(chunk[:LOG_CAP - kept])
                    kept += min(len(chunk), LOG_CAP - kept)
                if kept >= LOG_CAP:
                    truncated = True
            if truncated:
                output.write(b'\n[output truncated]\n')
        if not timed_out:
            proc.wait(timeout=max(.1, deadline - time.monotonic()))
    except subprocess.TimeoutExpired:
        timed_out = True
    finally:
        if timed_out:
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                proc.wait(timeout=10)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.wait()
        proc.stdout.close()
    return proc.returncode, timed_out


def verify(args: argparse.Namespace) -> dict:
    work = args.work.resolve()
    if work.exists():
        raise VerifyError('work directory must not exist')
    work.mkdir(parents=True)
    log = work / 'verify.log'
    result = {'status': 'failed', 'commit': args.commit, 'contract_commit': None,
              'log': str(log), 'claim': None}
    try:
        env = tools_env(args.trusted)
        if platform.system() == 'Linux':
            linux_preflight(env)
        contract = subprocess.run(['git', '-C', str(args.trusted), 'rev-parse', 'HEAD'],
                                  check=True, text=True, capture_output=True, timeout=10).stdout.strip()
        result['contract_commit'] = contract
        if not re.fullmatch(r'[0-9a-f]{40}|[0-9a-f]{64}', contract):
            raise VerifyError('trusted checkout has no canonical commit')
        source = work / 'source'
        if args.local:
            shutil.copytree(args.local, source, symlinks=True)
        else:
            fetch_pr(args.repository, args.pr, args.commit, source)
        policy = check(source)
        result['claim'] = policy['claim']
        if not policy['ok']:
            result.update(status='policy_rejected', errors=policy['errors'])
            log.write_text('\n'.join(policy['errors']) + '\n')
            return result
        project = work / 'project'
        project.mkdir()
        for name in ('lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'SigGolf.lean'):
            shutil.copy2(args.trusted / name, project / name)
        shutil.copytree(args.trusted / 'SigGolf', project / 'SigGolf')
        with (project / 'lakefile.lean').open('a') as out:
            out.write('\nlean_lib Solution\n')
        shutil.copytree(source / 'SigGolfCandidate', project / 'SigGolfCandidate')
        shutil.copy2(source / 'Solution.lean', project / 'Solution.lean')
        challenge = (args.trusted / 'verifier' / 'Challenge.lean.in').read_text()
        for key, value in policy['claim'].items():
            challenge = challenge.replace('{{' + key + '}}', str(value))
        (project / 'SigGolf' / 'Challenge.lean').write_text(challenge)
        clone_tree(args.trusted / '.lake', project / '.lake')
        for name in ('SigGolfCandidate', 'Solution'):
            for folder in (project / '.lake' / 'build' / 'lib' / 'lean', project / '.lake' / 'build' / 'ir'):
                target = folder / name
                if target.is_dir():
                    shutil.rmtree(target)
                elif target.exists():
                    target.unlink()
        for folder in (project / '.lake' / 'build' / 'lib' / 'lean', project / '.lake' / 'build' / 'ir'):
            target = folder / 'SigGolf' / 'Challenge.olean'
            if target.exists():
                target.unlink()
        command = ['lake', 'env', env['COMPARATOR_BIN'], str(args.trusted / 'verifier' / 'comparator.json')]
        clean_env = {'PATH': f'{Path.home() / ".elan/bin"}:{os.environ.get("PATH", "/usr/bin:/bin")}',
                     'HOME': str(Path.home()), 'LANG': 'C.UTF-8',
                     'COMPARATOR_LANDRUN': env['COMPARATOR_LANDRUN'],
                     'COMPARATOR_LEAN4EXPORT': env['COMPARATOR_LEAN4EXPORT']}
        if platform.system() == 'Linux':
            command, clean_env = linux_command(command, project, env, [work / 'source', *args.hide])
        exit_code, timeout = run_checked(command, project, clean_env, log)
        if timeout:
            result['status'] = 'timeout'
        elif exit_code == 0 and 'Your solution is okay!' in log.read_text(errors='replace'):
            result.update(status='verified', score=policy['score'])
        else:
            result.update(status='rejected', reason=log.read_text(errors='replace')[-1200:])
        return result
    except (FetchError, VerifyError, OSError, subprocess.SubprocessError) as exc:
        result.update(status='failed', reason=str(exc)[:1200])
        return result


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument('--repository', default='leanEthereum/sig.golf-submissions')
    parser.add_argument('--pr', type=int)
    parser.add_argument('--commit')
    parser.add_argument('--local', type=Path)
    parser.add_argument('--trusted', type=Path, default=TRUSTED)
    parser.add_argument('--work', type=Path)
    parser.add_argument('--hide', type=Path, action='append', default=[])
    parser.add_argument('--cleanup', action='store_true')
    args = parser.parse_args()
    if bool(args.local) == bool(args.pr and args.commit):
        parser.error('provide either --local or both --pr and --commit')
    args.trusted = args.trusted.resolve()
    if args.work is None:
        args.work = Path(tempfile.mkdtemp(prefix='sig-verify-'))
        args.work.rmdir()
    result = verify(args)
    if args.cleanup and args.work.exists():
        try:
            # Candidate code can change permissions inside its writable build tree.
            for directory, children, _ in os.walk(args.work, followlinks=False):
                os.chmod(directory, os.stat(directory).st_mode | 0o700)
                for child in children:
                    path = Path(directory) / child
                    if not path.is_symlink():
                        os.chmod(path, path.stat().st_mode | 0o700)
            shutil.rmtree(args.work)
        except OSError as exc:
            result.update(status='failed', reason=f'workspace cleanup failed: {exc}')
    print(json.dumps(result, sort_keys=True))
    return 0 if result['status'] == 'verified' else 1


if __name__ == '__main__':
    raise SystemExit(main())
