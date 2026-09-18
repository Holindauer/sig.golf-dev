"""Settings from the environment. Everything has a localhost default."""
from __future__ import annotations

import os
import re
from dataclasses import dataclass
from pathlib import Path
from urllib.parse import urlsplit

SERVICE_DIR = Path(__file__).resolve().parent.parent
DEFAULT_REPO_ROOT = SERVICE_DIR.parent


@dataclass
class Settings:
    environment: str = os.environ.get("SIG_ENV", "development")
    role: str = os.environ.get("SIG_ROLE", "web")
    repo_root: Path = Path(os.environ.get("SIG_REPO_ROOT", str(DEFAULT_REPO_ROOT))).resolve()
    data_dir: Path = Path(os.environ.get("SIG_DATA_DIR", str(SERVICE_DIR / "data"))).resolve()
    work_dir: Path | None = Path(os.environ["SIG_WORK_DIR"]).resolve() if os.environ.get("SIG_WORK_DIR") else None
    base_url: str = os.environ.get("SIG_BASE_URL", "http://localhost:8000").rstrip("/")
    github_webhook_secret: str = os.environ.get("GITHUB_WEBHOOK_SECRET", "")
    github_token: str = os.environ.get("GITHUB_TOKEN", "")
    contract_repo: str = os.environ.get("SIG_CONTRACT_REPO", "")   # owner/name of the public repository
    queue_cap: int = int(os.environ.get("SIG_QUEUE_CAP", "20"))
    max_inflight_per_user: int = int(os.environ.get("SIG_MAX_INFLIGHT_PER_USER", "2"))
    # Development only: run the isolated verifier without its Linux sandbox (verify_submission --insecure-local).
    insecure_local: bool = os.environ.get("SIG_INSECURE_LOCAL", "0") == "1"
    database_url: str = ""

    def __post_init__(self) -> None:
        if self.environment not in {"development", "production"}:
            raise ValueError("SIG_ENV must be development or production")
        if self.role not in {"web", "worker"}:
            raise ValueError("SIG_ROLE must be web or worker")
        if self.queue_cap < 1 or self.max_inflight_per_user < 1:
            raise ValueError("queue limits must be positive")
        url = urlsplit(self.base_url)
        if (url.scheme not in {"http", "https"} or not url.netloc or url.username or url.password
                or url.query or url.fragment or url.path):
            raise ValueError("SIG_BASE_URL must be an http(s) origin without credentials, a path or a query")
        if self.contract_repo and not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]{0,38}/[A-Za-z0-9_.-]{1,100}", self.contract_repo):
            raise ValueError("SIG_CONTRACT_REPO must be owner/repository")
        if self.environment == "production":
            if url.scheme != "https" or not self.contract_repo:
                raise ValueError("production requires an HTTPS origin and contract repository")
            if self.insecure_local:
                raise ValueError("production never runs the verifier without its sandbox")
            if self.role == "web" and (not self.github_token or len(self.github_webhook_secret) < 32):
                raise ValueError("the production web service requires a GitHub token and a webhook secret of at least 32 characters")
            if self.role == "worker" and (self.github_token or self.github_webhook_secret):
                raise ValueError("the production verifier worker must not receive GitHub secrets")
        self.data_dir.mkdir(parents=True, exist_ok=True)
        (self.data_dir / "logs").mkdir(exist_ok=True)
        self.work_dir = (self.work_dir or self.data_dir / "work").resolve()
        self.work_dir.mkdir(parents=True, exist_ok=True)
        self.database_url = os.environ.get("SIG_DATABASE_URL", f"sqlite:///{self.data_dir / 'sig.db'}")


settings = Settings()
