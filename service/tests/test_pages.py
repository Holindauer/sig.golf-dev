"""The pages: home with Spacetime and Pareto tabs, submission and solver pages, rules, llms.txt."""
from __future__ import annotations

import copy
import json
import re
import tempfile
import unittest
from datetime import timedelta
from pathlib import Path
from unittest.mock import patch

from fastapi.testclient import TestClient
from sqlalchemy import create_engine
from sqlalchemy.orm import Session
from sqlalchemy.pool import StaticPool

from app import contract, main
from app.config import settings
from app.db import Base, Submission, User, get_session, utcnow


class PageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.patch = patch.object(settings, 'data_dir', Path(self.temp.name))
        self.patch.start()
        self.engine = create_engine('sqlite://', connect_args={'check_same_thread': False}, poolclass=StaticPool)
        Base.metadata.create_all(self.engine)
        self.session = Session(self.engine, expire_on_commit=False)
        main.app.dependency_overrides[get_session] = lambda: self.session
        self.client = TestClient(main.app)

    def tearDown(self):
        self.client.close()
        main.app.dependency_overrides.clear()
        self.session.close()
        self.engine.dispose()
        self.patch.stop()
        self.temp.cleanup()

    def seed(self):
        alice, bob = User(login='alice', github_id=1), User(login='bob', github_id=2)
        self.session.add_all([alice, bob])
        self.session.commit()
        rows = [(alice, 2000, 200, True, 3), (bob, 1500, 300, True, 2), (alice, 2100, 210, False, 1)]
        subs = []
        for i, (user, sigma, hverify, record, days) in enumerate(rows):
            sub = Submission(track='full', user_id=user.id, source_repo='https://github.com/x/y.git', commit=f'{i:040x}',
                             sigma=sigma, hverify=hverify, score=str(sigma * hverify), status='verified',
                             is_record=record, record_at=utcnow() - timedelta(days=days) if record else None,
                             finished_at=utcnow() - timedelta(days=days), pr_number=10 + i,
                             pr_url=f'https://github.com/x/y/pull/{10 + i}', assisted_by='Fable 5.1' if i == 0 else None)
            self.session.add(sub)
            subs.append(sub)
        pending = Submission(track='full', user_id=bob.id, source_repo='https://github.com/x/y.git', commit='f' * 40,
                             status='pending', pr_number=20)
        self.session.add(pending)
        self.session.commit()
        return subs

    def test_home_shows_objective_tabs_and_closed_admission(self):
        html = self.client.get('/').text
        self.assertIn('minimize', html)
        self.assertIn('|σ| × V', html)
        self.assertIn('data-view="spacetime"', html)
        self.assertIn('data-view="pareto"', html)
        self.assertIn('Submissions are not open yet', html)
        self.assertIn('No submissions yet', html)
        self.assertIn('rom256-input64-ceil-v1', html)

    def test_home_ranks_records_and_marks_the_frontier(self):
        subs = self.seed()
        html = self.client.get('/').text
        rows = re.findall(r'<tr class="lb-row record( current)?"[^>]*data-score="(\d+)"', html)
        spacetime_scores = [int(score) for _, score in rows[:2]]
        self.assertEqual(spacetime_scores, [400000, 450000])
        self.assertIn('data-score="400000"', html)
        self.assertIn('>frontier<', html)
        self.assertIn('verified · awaiting merge', html)          # the unmerged verified head
        self.assertIn('s-pending', html)
        points = json.loads(re.search(r'<script id="chart-points" type="application/json">(.*?)</script>', html, re.S).group(1))
        self.assertEqual([p['value'] for p in points], [400000])   # only records that lowered the best score
        pareto = json.loads(re.search(r'<script id="pareto-points" type="application/json">(.*?)</script>', html, re.S).group(1))
        self.assertEqual({p['id'] for p in pareto if p['frontier']}, {subs[0].id, subs[1].id})
        self.assertIn('Fable 5.1', html)

    def test_open_admission_changes_the_notice(self):
        cfg = copy.deepcopy(contract.load())
        cfg['tracks'][0]['admission'] = 'open'
        with patch.object(contract, 'load', return_value=cfg):
            html = self.client.get('/').text
        self.assertIn('Submissions are open', html)
        self.assertNotIn('not open yet', html)

    def test_submission_and_solver_pages(self):
        subs = self.seed()
        page = self.client.get(f'/submissions/{subs[1].id}')
        self.assertEqual(page.status_code, 200)
        self.assertIn('450,000', page.text)
        self.assertIn('1,500', page.text)
        self.assertIn('frontier', page.text)
        self.assertIn('record', page.text)
        self.assertEqual(self.client.get(f'/submissions/{subs[1].id}/log').text, '(no log yet)')
        solver = self.client.get('/solvers/alice')
        self.assertEqual(solver.status_code, 200)
        self.assertIn('github.com/alice', solver.text)
        self.assertEqual(self.client.get('/solvers/nobody').status_code, 404)
        self.assertEqual(self.client.get('/submissions/nope').status_code, 404)

    def test_rules_serve_the_specification_itself(self):
        rules = self.client.get('/rules')
        self.assertEqual(rules.status_code, 200)
        self.assertIn('DRAFT v0.', rules.text)
        self.assertIn('leanSPHINCS', rules.text)

    def test_llms_txt_points_agents_at_the_contract(self):
        text = self.client.get('/llms.txt').text
        self.assertIn('sig.golf', text)
        self.assertIn('submissions/full', text)
        self.assertIn(settings.base_url + '/submissions/<id>', text)


if __name__ == '__main__':
    unittest.main()
