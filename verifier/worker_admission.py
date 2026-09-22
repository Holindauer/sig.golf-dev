"""Cooperative, per-checkout admission; not a global scheduler or cgroup quota."""

from contextlib import contextmanager
import fcntl
import os
from pathlib import Path
import stat


class WorkerBusy(RuntimeError):
    pass


@contextmanager
def worker_slot(results: Path):
    """Hold one kernel lock from before capture through receipt publication.

    Never unlink the lock: replacing its inode would permit two concurrent
    holders. Do not inherit the descriptor into compiler/comparator processes.
    A killed owner releases the lock, but this does not kill a detached service.
    """
    descriptor = os.open(results / ".worker.lock",
                         os.O_CREAT | os.O_RDWR | os.O_CLOEXEC | os.O_NOFOLLOW | os.O_NONBLOCK,
                         0o600)
    try:
        if not stat.S_ISREG(os.fstat(descriptor).st_mode):
            raise RuntimeError("worker lock must be a regular file")
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise WorkerBusy("another verification owns this checkout; retry later") from error
        yield
    finally:
        os.close(descriptor)
