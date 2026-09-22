"""A PR's latest checked head determines whether its notes remain published."""
import json
import unittest
from datetime import timedelta
from unittest.mock import patch

from sqlalchemy import create_engine
from sqlalchemy.orm import Session

from app import records
from app.db import Base, Submission, User, utcnow
from tests.support import EPOCH


class JournalHeadsTests(unittest.TestCase):
    def test_latest_head_removing_notes_hides_previous_notes(self):
        self.check_latest(None)

    def test_latest_head_with_notes_replaces_previous_notes(self):
        self.check_latest('New notes')

    def check_latest(self, notes):
        engine = create_engine('sqlite://')
        self.addCleanup(engine.dispose)
        Base.metadata.create_all(engine)
        with patch('app.contract.contract_id', return_value=EPOCH), Session(engine) as session:
            user = User(login='alice')
            session.add(user)
            session.flush()
            now = utcnow()
            for commit, text, at in [('a', 'Old notes', now - timedelta(seconds=1)), ('b', notes, now)]:
                session.add(Submission(track='full', user_id=user.id, source_repo='https://github.com/a/b.git',
                    commit=commit * 40, status='verified', pr_number=1,
                    pr_url='https://github.com/a/b/pull/1', finished_at=at,
                    detail=json.dumps({'notes': text, 'contract': EPOCH})))
            session.commit()
            self.assertNotIn('Old notes', [entry['sub'].notes for entry in records.journal(session)])
            self.assertEqual([entry['sub'].notes for entry in records.journal(session)], [notes] if notes else [])
            self.assertEqual(records.journal(session, 'nope'), [])


if __name__ == '__main__':
    unittest.main()
