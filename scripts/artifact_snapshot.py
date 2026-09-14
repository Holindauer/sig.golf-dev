"""Capture only declared Lean module artifacts after compiler cgroup termination."""
import os
from pathlib import Path
import stat
from source_bundle import manifest

SUFFIXES = ('.olean', '.olean.private', '.olean.server', '.ilean', '.olean.hash',
            '.ilean.hash', '.trace')
MAX_FILE = 256 * 1024 * 1024
MAX_TOTAL = 2 * 1024 * 1024 * 1024


def capture_artifacts(root, modules, prefix="LeanSphincs.Submission", required_modules=None):
    components = prefix.split(".")
    if any(not c.isidentifier() or not c.isascii() for c in components):
        raise ValueError("invalid organizer module prefix")
    # No-follow every directory component beneath the private project.
    fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW)
    try:
        for component in ('.lake', 'build', 'lib', 'lean', *components):
            child = os.open(component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW, dir_fd=fd)
            os.close(fd)
            fd = child
        names = os.listdir(fd)
        allowed = {m + suffix for m in modules for suffix in SUFFIXES}
        if set(names) - allowed:
            raise RuntimeError('unexpected module artifact paths')
        required = set(modules) & {'Scheme', 'Solution'} if required_modules is None else set(required_modules)
        if not required <= set(modules):
            raise ValueError('required modules outside source manifest')
        if not {m + '.olean' for m in required} <= set(names):
            raise RuntimeError('missing compiled modules')
        bundle, total = {}, 0
        for name in sorted(names):
            child = os.open(name, os.O_RDONLY | os.O_NONBLOCK | os.O_NOFOLLOW, dir_fd=fd)
            with os.fdopen(child, 'rb') as stream:
                info = os.fstat(stream.fileno())
                if not stat.S_ISREG(info.st_mode) or info.st_size > MAX_FILE:
                    raise RuntimeError('invalid artifact type or size')
                data = stream.read(min(MAX_FILE, MAX_TOTAL - total) + 1)
                total += len(data)
                if len(data) > MAX_FILE or total > MAX_TOTAL:
                    raise RuntimeError('artifact size cap exceeded')
                bundle[name] = data
        return bundle
    finally:
        os.close(fd)


def freeze_artifacts(compiler, verifier, modules, prefix="LeanSphincs.Submission", required_modules=None):
    bundle = capture_artifacts(compiler, modules, prefix, required_modules)
    destination = verifier / ".lake/build/lib/lean" / prefix.replace(".", "/")
    for name, data in bundle.items():
        with (destination / name).open('xb') as stream:
            stream.write(data)
        (destination / name).chmod(0o400)
    destination.chmod(0o500)
    return manifest(bundle)
