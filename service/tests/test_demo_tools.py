"""Demo controls must not let an operator seed a production site accidentally."""
import unittest
from types import SimpleNamespace
from unittest.mock import patch

from sqlalchemy import create_engine, select
from sqlalchemy.orm import Session

import seed_demo
from app import records
from app.config import SERVICE_DIR
from app.db import Base, Submission
from app.visibility import visible


class DemoGuardTests(unittest.TestCase):
    def test_visibility_obeys_demo_mode_for_existing_rows(self):
        for phony in (True, False):
            with patch('app.visibility.settings', SimpleNamespace(phony=phony)):
                self.assertEqual(visible(SimpleNamespace(track='full', detail_dict={'demo': True})), phony)
                self.assertTrue(visible(SimpleNamespace(track='full', detail_dict={})))
                self.assertFalse(visible(SimpleNamespace(track='retired', detail_dict={})))

    def test_default_seed_and_refresh_command_preserve_existing_rows(self):
        config = SimpleNamespace(environment='development', base_url='http://localhost:8000',
                                 database_url=f"sqlite:///{(SERVICE_DIR / 'data').resolve() / 'sig.db'}")
        for args in ([], ['--refresh']):
            with self.subTest(args=args), patch('app.config.settings', config), \
                    patch('sys.argv', ['seed_demo.py', *args]), \
                    patch.object(seed_demo.Base.metadata, 'create_all'), \
                    patch.object(seed_demo, 'SessionLocal'), \
                    patch.object(seed_demo, 'refresh', return_value=0) as refresh, \
                    patch.object(seed_demo, 'remove') as remove:
                seed_demo.main()
                refresh.assert_called_once()
                remove.assert_not_called()

    def test_force_cannot_bypass_production_or_nonlocal_site_guard(self):
        for environment, base_url in [('production', 'https://sig.example'),
                                      ('development', 'https://sig.example')]:
            with self.subTest(environment=environment):
                config = SimpleNamespace(environment=environment, base_url=base_url)
                with patch('app.config.settings', config), patch('sys.argv', ['seed_demo.py', '--force']), \
                        patch.object(seed_demo.Base.metadata, 'create_all') as create_db:
                    with self.assertRaisesRegex(SystemExit, 'only available in development'):
                        seed_demo.main()
                    create_db.assert_not_called()

    def test_fixtures_form_a_consistent_record_history(self):
        engine = create_engine('sqlite://')
        self.addCleanup(engine.dispose)
        Base.metadata.create_all(engine)
        with Session(engine, expire_on_commit=False) as session:
            self.assertEqual(seed_demo.add(session), len(seed_demo.ROWS))
            self.assertEqual(seed_demo.refresh(session), 0)
            rows = list(session.scalars(select(Submission).order_by(Submission.record_at)))
            self.assertTrue(all(r.detail and '"demo": true' in r.detail for r in rows))
            with patch('app.visibility.settings', SimpleNamespace(phony=True)):
                recs = records.records(session, 'full')
                self.assertEqual(len(recs), sum(r['is_record'] for r in seed_demo.ROWS))
                # Every fixture record is either the best score so far or a frontier point when it was set.
                for i, s in enumerate(recs):
                    self.assertTrue(records.improves(recs[:i], s.sigma, s.hverify), s.id)
                self.assertEqual(records.current_record(session, 'full').score_int, 5632 * 1160)
            self.assertEqual(seed_demo.remove(session), len(seed_demo.ROWS))


if __name__ == '__main__':
    unittest.main()
