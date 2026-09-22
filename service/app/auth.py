"""Users come from GitHub pull requests; there is no login and no token."""
from __future__ import annotations

from sqlalchemy import select
from sqlalchemy.orm import Session

from .db import User


def get_or_create_user(session: Session, login: str, github_id: int | None = None,
                       name: str | None = None, avatar_url: str | None = None) -> User:
    """A GitHub account is its numeric id; the login is a label that can change hands. A row is never
    adopted through its login: a local user (no id, such as a local job's or a demo solver) stays local, and a row
    holding a login that GitHub has since given to someone else gives the login up."""
    if github_id is None:                                   # local users: local jobs, the demo seed
        user = session.scalars(select(User).where(User.login == login, User.github_id.is_(None))).first()
        if user is None:
            user = User(login=login, name=name, avatar_url=avatar_url)
            session.add(user)
        session.commit()
        return user
    user = session.scalars(select(User).where(User.github_id == github_id)).first()
    holder = session.scalars(select(User).where(User.login == login)).first()
    if holder is not None and holder is not user:
        holder.login = f"{holder.login}~{holder.id}"        # "~" cannot occur in a GitHub login
        session.flush()
    if user is None:
        user = User(login=login, github_id=github_id, name=name, avatar_url=avatar_url)
        session.add(user)
    else:
        user.login, user.name, user.avatar_url = login, name or user.name, avatar_url or user.avatar_url
    session.commit()
    return user
