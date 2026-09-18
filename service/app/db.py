"""Database: users and submissions, in SQLite (WAL) under the data directory."""
from __future__ import annotations

import fcntl
import json
import uuid
from contextlib import contextmanager
from datetime import datetime, timezone

from sqlalchemy import BigInteger, Boolean, DateTime, Float, ForeignKey, Integer, String, Text, create_engine, event
from sqlalchemy.orm import DeclarativeBase, Mapped, mapped_column, relationship, sessionmaker

from .config import settings


def utcnow() -> datetime:
    """Naive UTC, which is what every backend stores faithfully."""
    return datetime.now(timezone.utc).replace(tzinfo=None)


class Base(DeclarativeBase):
    pass


class User(Base):
    __tablename__ = "users"
    id: Mapped[int] = mapped_column(primary_key=True)
    github_id: Mapped[int | None] = mapped_column(Integer, unique=True, nullable=True)
    login: Mapped[str] = mapped_column(String(80), unique=True)
    name: Mapped[str | None] = mapped_column(String(200), nullable=True)
    avatar_url: Mapped[str | None] = mapped_column(String(400), nullable=True)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=utcnow)
    submissions: Mapped[list["Submission"]] = relationship(back_populates="user")


class Submission(Base):
    """One verified-or-not head. Score is the exact integer sigma * hverify, kept as a decimal string
    because it can exceed 64 bits; ordering is done in Python on the small record set."""
    __tablename__ = "submissions"
    id: Mapped[str] = mapped_column(String(32), primary_key=True, default=lambda: uuid.uuid4().hex)
    track: Mapped[str] = mapped_column(String(16), index=True)
    user_id: Mapped[int] = mapped_column(ForeignKey("users.id"), index=True)
    source_repo: Mapped[str] = mapped_column(String(400))
    commit: Mapped[str] = mapped_column(String(64))
    sigma: Mapped[int | None] = mapped_column(BigInteger, nullable=True)
    hverify: Mapped[int | None] = mapped_column(BigInteger, nullable=True)
    score: Mapped[str | None] = mapped_column(String(64), nullable=True)
    status: Mapped[str] = mapped_column(String(20), default="pending", index=True)
    is_record: Mapped[bool] = mapped_column(Boolean, default=False)
    record_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    baseline: Mapped[bool] = mapped_column(Boolean, default=False)
    assisted_by: Mapped[str | None] = mapped_column(String(120), nullable=True)
    description: Mapped[str | None] = mapped_column(Text, nullable=True)
    co_authors: Mapped[str] = mapped_column(Text, default="[]")
    pr_number: Mapped[int | None] = mapped_column(Integer, nullable=True)
    pr_url: Mapped[str | None] = mapped_column(String(400), nullable=True)
    created_at: Mapped[datetime] = mapped_column(DateTime, default=utcnow, index=True)
    started_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    finished_at: Mapped[datetime | None] = mapped_column(DateTime, nullable=True)
    duration_s: Mapped[float | None] = mapped_column(Float, nullable=True)
    detail: Mapped[str] = mapped_column(Text, default="{}")
    log_path: Mapped[str | None] = mapped_column(String(400), nullable=True)
    user: Mapped[User] = relationship(back_populates="submissions")

    @property
    def score_int(self) -> int | None:
        try:
            return int(self.score) if self.score is not None else None
        except ValueError:
            return None

    @property
    def scored(self) -> bool:
        return self.score_int is not None and self.sigma is not None and self.hverify is not None

    @property
    def co_authors_list(self) -> list[str]:
        try:
            value = json.loads(self.co_authors or "[]")
            return [name for name in value if isinstance(name, str)] if isinstance(value, list) else []
        except (ValueError, TypeError):
            return []

    @property
    def detail_dict(self) -> dict:
        try:
            value = json.loads(self.detail or "{}")
            return value if isinstance(value, dict) else {}
        except (ValueError, TypeError):
            return {}

    @property
    def commit_url(self) -> str | None:
        if self.source_repo.startswith("https://github.com/"):
            return f"{self.source_repo.removesuffix('.git')}/commit/{self.commit}"
        return None


class GithubReport(Base):
    """Durable result outbox. A failed GitHub request must not lose a proof's verdict."""
    __tablename__ = "github_reports"
    submission_id: Mapped[str] = mapped_column(ForeignKey("submissions.id", ondelete="CASCADE"), primary_key=True)
    version: Mapped[int] = mapped_column(Integer, default=1)
    attempts: Mapped[int] = mapped_column(Integer, default=0)
    next_attempt: Mapped[datetime] = mapped_column(DateTime, default=utcnow, index=True)


def schedule_report(session, sub: Submission) -> None:
    if sub.pr_number is None:
        return
    session.flush()
    report = session.get(GithubReport, sub.id)
    if report is None:
        session.add(GithubReport(submission_id=sub.id))
    else:
        report.version += 1
        report.next_attempt = utcnow()


is_sqlite = settings.database_url.startswith("sqlite")
engine = create_engine(settings.database_url, connect_args={"check_same_thread": False} if is_sqlite else {})
if is_sqlite:
    @event.listens_for(engine, "connect")
    def _sqlite_pragmas(dbapi_conn, _):
        cur = dbapi_conn.cursor()
        cur.execute("PRAGMA journal_mode=WAL")
        cur.execute("PRAGMA busy_timeout=5000")
        cur.execute("PRAGMA foreign_keys=ON")
        cur.close()

SessionLocal = sessionmaker(engine, expire_on_commit=False)


@contextmanager
def local_lock(name: str, *, blocking: bool = True):
    """Serialize one-host service work across threads and processes. Keep the lock file in place:
    unlinking a locked inode would let another worker bypass it. Locks die with the process."""
    with (settings.data_dir / f"{name}.lock").open("a") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | (0 if blocking else fcntl.LOCK_NB))
        try:
            yield
        finally:
            fcntl.flock(lock, fcntl.LOCK_UN)


def init_db() -> None:
    with local_lock("schema"):
        Base.metadata.create_all(engine)


def get_session():
    with SessionLocal() as session:
        yield session
