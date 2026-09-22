"""Record promotion, durable reporting, worker exclusivity and pipeline result checks."""
from __future__ import annotations

import json
import subprocess
import tempfile
import unittest
from datetime import timedelta
from pathlib import Path
from unittest.mock import Mock, patch

import httpx
from fastapi.testclient import TestClient
from sqlalchemy import create_engine, select
from sqlalchemy.orm import sessionmaker
from sqlalchemy.pool import StaticPool

from app import contract, github, main, records, resync, source_archive, worker
from app.config import settings
from app.db import Base, GithubReport, Submission, User, legacy_pr_submission_id, local_lock, pr_submission_id, schedule_report, utcnow
from tests.support import EPOCH, ROOT, open_admission, pin_contract, write_root


class ServiceWorkerTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.data = Path(self.temp.name)
        (self.data / 'work').mkdir()
        (self.data / 'logs').mkdir()
        pin_contract(self)
        open_admission(self)
        self.engine = create_engine('sqlite://', connect_args={'check_same_thread': False}, poolclass=StaticPool)
        Base.metadata.create_all(self.engine)
        self.sessions = sessionmaker(self.engine, expire_on_commit=False)
        self.patches = [patch.object(settings, 'data_dir', self.data),
                        patch.object(settings, 'work_dir', self.data / 'work'),
                        patch.object(settings, 'contract_repo', 'owner/core'),
                        patch.object(settings, 'submissions_repo', 'owner/repo'),
                        patch.object(settings, 'github_token', ''),
                        patch('app.worker.SessionLocal', self.sessions), patch('app.main.SessionLocal', self.sessions)]
        for p in self.patches:
            p.start()
        with self.sessions() as session:
            user = User(login='proof-author')
            session.add(user)
            session.commit()
            self.user_id = user.id
        self.counter = 0

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.engine.dispose()
        self.temp.cleanup()

    def submission(self, *, sigma=2274, hverify=160, status='verified', record=False, pr=7, commit=None):
        self.counter += 1
        commit = commit or f'{self.counter:040x}'
        scored = sigma is not None and hverify is not None
        with self.sessions() as session:
            sub = Submission(user_id=self.user_id, track='full', status=status,
                             sigma=sigma, hverify=hverify, score=str(sigma * hverify) if scored else None,
                             commit=commit, source_repo='https://github.com/author/repo.git',
                             pr_number=pr, pr_url=f'https://github.com/owner/repo/pull/{pr}' if pr else None,
                             is_record=record, detail=json.dumps({"contract": contract.contract_id()}),
                             record_at=utcnow() + timedelta(seconds=self.counter) if record else None,
                             finished_at=utcnow() if status in worker.TERMINAL_STATUSES else None)
            session.add(sub)
            session.commit()
            return sub

    def retain_source(self, sub, sigma=2274, hverify=160):
        root = self.data / ('input-' + sub.id)
        write_root(root, sigma=sigma, hverify=hverify)
        return source_archive.archives.save_source(source_archive.directory(), sub.id, root,
            source_repo=sub.source_repo, commit=sub.commit, track=sub.track,
            submission_root=contract.track(sub.track)['submission_root'], contract=sub.detail_dict['contract'])

    @staticmethod
    def result(sub, sigma=2274, hverify=160, status='verified', **extra):
        value = {'status': status, 'track': sub.track, 'commit': sub.commit, 'tail': 'bad proof', **extra}
        if status == 'verified':
            value.update(sigma=sigma, hverify=hverify, score=str(sigma * hverify))
        return value

    def verify(self, sub, sigma=2274, hverify=160, status='verified', **extra):
        """Let the worker finish checking `sub` with the given verdict."""
        with patch('app.worker.run_pipeline', return_value=(self.result(sub, sigma, hverify, status, **extra), None)):
            worker.process(sub.id)
        with self.sessions() as session:
            return session.get(Submission, sub.id)

    def test_retired_pending_and_publishing_jobs_do_not_run_or_block_active_tracks(self):
        retired = self.submission(status='pending', sigma=None, hverify=None, pr=40)
        publishing = self.submission(status='publishing', sigma=None, hverify=None, pr=41)
        with self.sessions() as session:
            session.get(Submission, retired.id).track = 'retired-track'
            session.get(Submission, publishing.id).track = 'other-retired'
            session.commit()
        with patch('app.worker.run_pipeline') as run:
            worker.process(retired.id)
            run.assert_not_called()
        active = self.submission(status='pending', sigma=None, hverify=None, pr=42)
        self.assertEqual(self.verify(active, status='rejected').status, 'rejected')
        with self.sessions() as session:
            self.assertEqual(session.get(Submission, retired.id).status, 'pending')
            self.assertEqual(session.get(Submission, publishing.id).status, 'publishing')

    def test_historical_and_unversioned_results_cannot_rank(self):
        for i, epoch in enumerate(('old-contract', None)):
            sub = self.submission(sigma=1, hverify=1, record=True, pr=20 + i)
            with self.sessions() as session:
                session.get(Submission, sub.id).detail = json.dumps({'contract': epoch})
                session.commit()
        with self.sessions() as session:
            self.assertIsNone(records.current_record(session, 'full'))
            self.assertEqual(records.frontier(session, 'full'), [])
            self.assertEqual(records.curve(session, 'full'), [])
            self.assertEqual(records.solver_count(session, 'full'), 0)
        fresh = self.submission(sigma=None, hverify=None, status='pending')
        self.assertTrue(self.verify(fresh).is_record)

    def test_same_head_can_be_checked_under_a_new_contract(self):
        with self.sessions() as session:
            user = session.get(User, self.user_id)
            first = main.queue_submission(session, user, 'full', 'https://github.com/a/b.git',
                                          'a' * 40, '', [], None, 7, 'https://github.com/owner/repo/pull/7')
            first.status = 'verified'
            session.commit()
            first_id = first.id
            with patch('app.contract.contract_id', return_value='f' * 64):
                second = main.queue_submission(session, user, 'full', 'https://github.com/a/b.git',
                                               'a' * 40, '', [], None, 7, 'https://github.com/owner/repo/pull/7')
                self.assertNotEqual(first_id, second.id)
                self.assertTrue(second.current_contract)
                self.assertFalse(first.current_contract)
                self.assertEqual(second.id, pr_submission_id('owner/repo', 7, 'a' * 40))
            self.assertEqual(session.get(Submission, first_id).status, 'verified')

    def test_queued_obsolete_contract_never_runs_against_new_contract(self):
        sub = self.submission(sigma=None, hverify=None, status='pending')
        with patch('app.contract.contract_id', return_value='f' * 64), patch('app.worker.run_pipeline') as run:
            worker.process(sub.id)
            run.assert_not_called()
        with self.sessions() as session:
            checked = session.get(Submission, sub.id)
            self.assertEqual(checked.status, 'failed')
            self.assertEqual(checked.detail_dict['contract'], EPOCH)
            self.assertFalse(checked.is_record)

    def test_contract_change_during_verification_fails_closed(self):
        sub = self.submission(sigma=None, hverify=None, status='pending')
        def pipeline(_):
            current.return_value = 'f' * 64
            return self.result(sub), None
        with patch('app.contract.contract_id', return_value=EPOCH) as current, \
             patch('app.worker.run_pipeline', side_effect=pipeline):
            worker.process(sub.id)
        with self.sessions() as session:
            checked = session.get(Submission, sub.id)
            self.assertEqual(checked.status, 'failed')
            self.assertFalse(checked.is_record)
            self.assertIsNone(checked.score)

    def test_first_verified_improvement_becomes_the_record_without_a_merge(self):
        sub = self.submission(sigma=None, hverify=None, status='pending')
        checked = self.verify(sub)
        self.assertTrue(checked.is_record)
        self.assertEqual((checked.sigma, checked.hverify, checked.score), (2274, 160, '363840'))
        self.assertEqual(checked.record_at, checked.finished_at)
        with self.sessions() as session:
            self.assertEqual(records.current_record(session, 'full').id, sub.id)
            self.assertIsNotNone(session.get(GithubReport, sub.id))   # the comment says "new record"

    def test_later_identical_metrics_never_take_the_record(self):
        first = self.submission(sigma=None, hverify=None, status='pending', pr=7)
        copy = self.submission(sigma=None, hverify=None, status='pending', pr=8)
        better = self.submission(sigma=None, hverify=None, status='pending', pr=9)
        self.assertTrue(self.verify(first, 2000, 200).is_record)
        self.assertFalse(self.verify(copy, 2000, 200).is_record)
        self.assertTrue(self.verify(better, 1900, 200).is_record)
        with self.sessions() as session:
            self.assertEqual([s.id for s in records.frontier(session, 'full')], [better.id, first.id])

    def test_frontier_extension_promotes_even_with_a_worse_product(self):
        first = self.submission(sigma=None, hverify=None, status='pending', pr=7)
        smaller_sig = self.submission(sigma=None, hverify=None, status='pending', pr=8)
        dominated = self.submission(sigma=None, hverify=None, status='pending', pr=9)
        self.assertTrue(self.verify(first, 2000, 200).is_record)          # 400,000
        self.assertTrue(self.verify(smaller_sig, 1500, 300).is_record)    # 450,000 but fewer bytes: frontier
        self.assertFalse(self.verify(dominated, 2100, 210).is_record)     # worse on both: no record
        with self.sessions() as session:
            recs = records.records(session, 'full')
            self.assertEqual({s.id for s in recs}, {first.id, smaller_sig.id})
            self.assertEqual([s.sigma for s in records.pareto(recs)], [1500, 2000])
            self.assertEqual(records.current_record(session, 'full').id, first.id)
            front = session.get(Submission, smaller_sig.id)
            self.assertTrue(worker.beats_record(session, front))            # extends the frontier of the others
            self.assertFalse(worker.takes_lead(session, front))              # but records.json names the best score
            self.assertTrue(worker.takes_lead(session, session.get(Submission, first.id)))
            self.assertFalse(worker.beats_record(session, session.get(Submission, dominated.id)))

    def test_demo_records_never_block_a_real_record(self):
        demo = self.submission(sigma=1, hverify=1, pr=8, record=True)
        with self.sessions() as session:
            session.get(Submission, demo.id).detail = json.dumps({'demo': True})
            session.commit()
        sub = self.submission(sigma=None, hverify=None, status='pending')
        self.assertTrue(self.verify(sub).is_record)

    def test_pull_requests_of_another_repository_never_become_records(self):
        old = self.submission(sigma=None, hverify=None, status='pending')
        with self.sessions() as session:
            session.get(Submission, old.id).pr_url = 'https://github.com/owner/core/pull/7'
            session.commit()
        self.assertFalse(self.verify(old).is_record)
        new = self.submission(sigma=None, hverify=None, status='pending')
        self.assertTrue(self.verify(new).is_record)
        with self.sessions() as session:
            self.assertEqual(records.current_record(session, 'full').id, new.id)

    def test_core_handlers_never_contact_github_for_proof_intake(self):
        with patch('app.main.github.get_pr') as get_pr:
            self.assertFalse(main.handle_pull_request('owner/core', 7, 'a' * 40)['queued'])
            get_pr.assert_not_called()

    def test_submission_pr_queues_its_fork_head_against_the_core_verifier(self):
        pr = {'state': 'open', 'changed_files': 1, 'body': 'A proof.',
              'user': {'login': 'alice', 'id': 42},
              'base': {'ref': 'main', 'repo': {'default_branch': 'main'}},
              'head': {'sha': 'b' * 40, 'repo': {'clone_url': 'https://github.com/alice/entries.git'}}}
        with patch('app.main.github.get_pr', return_value=pr), \
             patch('app.main.github.pr_track', return_value=('full', [])):
            queued = main.handle_pull_request('owner/repo', 9, 'b' * 40)
        self.assertTrue(queued['queued'])
        with self.sessions() as session:
            sub = session.get(Submission, queued['id'])
            self.assertEqual(sub.pr_repository, 'owner/repo')
            self.assertEqual(sub.source_repo, 'https://github.com/alice/entries.git')
            self.assertEqual(sub.commit, 'b' * 40)
            self.retain_source(sub)
            proc = Mock(returncode=0)
            proc.communicate.return_value = (json.dumps(self.result(sub)), '')
            with patch('app.worker.subprocess.Popen', return_value=proc) as launch:
                self.assertEqual(worker.run_pipeline(sub)[0]['status'], 'verified')
                command = launch.call_args.args[0]
                self.assertEqual(command[1], str(settings.repo_root / 'verifier/verify.py'))
                self.assertEqual(command[2], 'full')
                self.assertEqual(command[command.index('--source') + 1], sub.source_repo)
                self.assertEqual(command[command.index('--commit') + 1], sub.commit)
                self.assertEqual(command[command.index('--hide') + 1], str(settings.data_dir))
                self.assertEqual(command[command.index('--archive-dir') + 1], str(source_archive.directory()))
                self.assertEqual(command[command.index('--archive-id') + 1], sub.id)
                self.assertIn('--json', command)
                self.assertIn('--keep', command)
                self.assertNotIn('--insecure-local', command)
                self.assertEqual(launch.call_args.kwargs['cwd'], settings.repo_root)

    def test_only_development_may_skip_the_sandbox(self):
        sub = self.submission()
        self.retain_source(sub)
        proc = Mock(returncode=0)
        proc.communicate.return_value = (json.dumps(self.result(sub)), '')
        with patch('app.worker.subprocess.Popen', return_value=proc) as launch, \
                patch.object(settings, 'insecure_local', True):
            worker.run_pipeline(sub)
            self.assertIn('--insecure-local', launch.call_args.args[0])
            with patch.object(settings, 'environment', 'production'):
                worker.run_pipeline(sub)
                self.assertNotIn('--insecure-local', launch.call_args.args[0])

    def test_draft_pr_never_enters_the_queue_or_receives_a_receipt(self):
        with patch('app.main.github.get_pr', return_value={'draft': True}), \
             patch('app.main.github.pr_track') as files, \
             patch('app.main.queue_submission') as queue, \
             patch('app.main.github.post_comment') as comment:
            result = main.handle_pull_request('owner/repo', 9, 'b' * 40)
            self.assertEqual(result, {'queued': False, 'reason': 'draft pull request'})
            files.assert_not_called()
            queue.assert_not_called()
            comment.assert_not_called()

    def test_pr_returned_to_draft_during_admission_is_not_queued(self):
        pr = {'state': 'open', 'draft': False, 'changed_files': 1, 'head': {'sha': 'b' * 40}}
        with patch('app.main.github.get_pr', side_effect=[pr, dict(pr, draft=True)]), \
             patch('app.main.github.pr_track', return_value=('full', [])), \
             patch('app.main.queue_submission') as queue:
            result = main.handle_pull_request('owner/repo', 9, 'b' * 40)
            self.assertEqual(result, {'queued': False, 'reason': 'draft pull request'})
            queue.assert_not_called()

    def test_pull_requests_not_targeting_the_default_branch_are_refused(self):
        pr = {'state': 'open', 'changed_files': 1, 'body': '', 'user': {'login': 'alice', 'id': 42},
              'base': {'ref': 'side', 'repo': {'default_branch': 'main'}},
              'head': {'sha': 'b' * 40, 'repo': {'clone_url': 'https://github.com/alice/entries.git'}}}
        with patch('app.main.github.get_pr', return_value=pr), \
             patch('app.main.github.pr_track', return_value=('full', [])), \
             patch('app.main.github.post_comment') as comment:
            self.assertFalse(main.handle_pull_request('owner/repo', 9, 'b' * 40)['queued'])
            comment.assert_called_once()
        self.assertFalse(github.targets_default_branch(pr))
        self.assertFalse(github.targets_default_branch({'base': {'ref': 'main', 'repo': {}}}))
        self.assertTrue(github.targets_default_branch({'base': {'ref': 'main', 'repo': {'default_branch': 'main'}}}))

    def test_notes_from_the_verifier_are_stored_but_not_rendered(self):
        sub = self.submission(sigma=None, hverify=None, status='pending')
        result = self.result(sub, status='rejected', notes='## Dead end\n\nThe averaging lemma loses a factor of two.')
        with patch('app.worker.run_pipeline', return_value=(result, None)):
            worker.process(sub.id)
        with self.sessions() as session:
            self.assertEqual(session.get(Submission, sub.id).notes, result['notes'])
            main.app.dependency_overrides[main.get_session] = lambda: session
            try:
                with patch('app.main.prepare_board'), TestClient(main.app) as client:
                    page = client.get(f'/submissions/{sub.id}').text
                    journal = client.get('/notes.md').text
            finally:
                main.app.dependency_overrides.clear()
        self.assertNotIn('The averaging lemma loses a factor of two.', page)   # agents read /notes.md
        self.assertIn('The averaging lemma loses a factor of two.', journal)

    def test_failed_proof_cannot_become_record(self):
        sub = self.submission(sigma=None, hverify=None, status='pending')
        checked = self.verify(sub, status='rejected')
        self.assertFalse(checked.is_record)
        self.assertEqual(checked.detail_dict['failure']['message'], 'bad proof')
        with self.sessions() as session:
            self.assertIsNone(records.current_record(session, 'full'))

    def test_local_job_never_becomes_a_record(self):
        sub = self.submission(pr=None)
        with self.sessions() as session:
            checked = session.get(Submission, sub.id)
            worker.promote(session, checked)
            session.commit()
            self.assertFalse(checked.is_record)
            self.assertIsNone(records.current_record(session, 'full'))

    def test_result_reports_are_durable_and_retried_without_reverification(self):
        sub = self.submission()
        with self.sessions() as session:
            schedule_report(session, session.get(Submission, sub.id))
            session.commit()
        with patch.object(settings, 'github_token', 'test'), patch('app.worker.report', side_effect=RuntimeError('offline')):
            worker.deliver_report(sub.id)
        with self.sessions() as session:
            pending = session.get(GithubReport, sub.id)
            self.assertEqual(pending.attempts, 1)
            self.assertGreater(pending.next_attempt, utcnow())
            pending.next_attempt = utcnow() - timedelta(seconds=1)
            session.commit()
        with patch.object(settings, 'github_token', 'test'), patch('app.worker.report', return_value=123) as report:
            worker.retry_reports()
            report.assert_called_once()
        with self.sessions() as session:
            self.assertIsNone(session.get(GithubReport, sub.id))
            self.assertEqual(session.get(Submission, sub.id).detail_dict['github_comment_id'], 123)

    def test_result_during_report_preserves_newer_pending_outbox_version(self):
        sub = self.submission(sigma=None, hverify=None, status='pending')
        with self.sessions() as session:
            schedule_report(session, session.get(Submission, sub.id))
            session.commit()
        def report(_sub, _history=None):
            self.verify(sub)
            return 123
        with patch.object(settings, 'github_token', 'test'), patch('app.worker.report', side_effect=report):
            worker.deliver_report(sub.id)
        with self.sessions() as session:
            self.assertIsNotNone(session.get(GithubReport, sub.id))
            checked = session.get(Submission, sub.id)
            self.assertTrue(checked.is_record)
            self.assertEqual(checked.detail_dict['github_comment_id'], 123)

    def test_verified_report_states_the_score_and_updates_the_same_comment(self):
        sub = self.submission(record=True)
        sub.detail = json.dumps({'github_comment_id': 123, 'contract': contract.contract_id()})
        with patch('app.worker.github.post_status') as status, patch('app.worker.github.update_comment') as update, \
             patch('app.worker.github.post_comment') as post:
            self.assertEqual(worker.report(sub), 123)
            self.assertIn('score 363840 = 2274 B × 160', status.call_args.args[3])
            self.assertIn('new record', status.call_args.args[3])
            self.assertEqual(status.call_args.args[0], 'owner/repo')
            self.assertEqual(update.call_args.args[:2], ('owner/repo', 123))
            post.assert_not_called()

    def test_historical_report_cannot_replace_the_current_commit_status(self):
        current = self.submission(status='rejected', sigma=None, hverify=None)
        historical = self.submission()
        historical.detail = json.dumps({'contract': 'old-contract'})
        with patch('app.worker.github.post_status') as status, \
             patch('app.worker.github.post_comment', return_value=123) as comment:
            worker.report(current)
            worker.report(historical)
        self.assertEqual([call.args[2] for call in status.call_args_list], ['failure'])
        self.assertIn('Historical contract result', comment.call_args.args[2])

    def test_pr_submission_ids_are_stable_and_failed_heads_requeue_under_the_same_id(self):
        pr = {'state': 'open', 'user': {'login': 'alice', 'id': 42},
              'base': {'ref': 'main', 'repo': {'default_branch': 'main'}},
              'head': {'sha': 'b' * 40, 'repo': {'clone_url': 'https://github.com/alice/entries.git'}}}
        with patch('app.main.github.get_pr', return_value=pr), \
             patch('app.main.github.pr_track', return_value=('full', [])):
            first = main.handle_pull_request('owner/repo', 9, 'b' * 40)
        self.assertEqual(first['id'], pr_submission_id('owner/repo', 9, 'b' * 40))
        with self.sessions() as session:
            sub = session.get(Submission, first['id'])
            sub.status = 'failed'
            session.commit()
        with patch('app.main.github.get_pr', return_value=pr), \
             patch('app.main.github.pr_track', return_value=('full', [])):
            again = main.handle_pull_request('owner/repo', 9, 'b' * 40)
        self.assertEqual(again['id'], first['id'])
        with self.sessions() as session:
            self.assertEqual(session.get(Submission, first['id']).status, 'pending')
            self.assertEqual(len(list(session.scalars(select(Submission)))), 1)

    def test_comment_records_every_verdict_of_the_pull_request(self):
        first = self.submission(sigma=2000, hverify=200, commit='a' * 40)
        with self.sessions() as session:
            second = Submission(user_id=self.user_id, track='full', status='rejected',
                                commit='c' * 40, source_repo='https://github.com/author/repo.git',
                                pr_number=7, pr_url='https://github.com/owner/repo/pull/7',
                                detail=json.dumps({'contract': contract.contract_id()}))
            session.add(second)
            schedule_report(session, second)
            session.commit()
        with patch.object(settings, 'github_token', 'test'), patch('app.worker.github.post_status'), \
             patch('app.worker.github.post_comment', return_value=9) as post:
            worker.deliver_report(second.id)
        body = post.call_args.args[2]
        verdicts = github.parse_verdicts(body)
        self.assertEqual([(v['commit'], v['status'], v['sigma'], v['score']) for v in verdicts],
                         [('a' * 40, 'verified', 2000, '400000'), ('c' * 40, 'rejected', None, None)])
        self.assertNotIn('--', body.split('<!-- sig-result')[1].split('-->')[0])

    def test_malformed_or_forged_verdict_blocks_are_ignored(self):
        self.assertEqual(github.parse_verdicts('no block'), [])
        self.assertEqual(github.parse_verdicts('<!-- sig-result\n{bad json\n-->'), [])
        bad = '<!-- sig-result\n{"version":1,"results":[{"track":"full","commit":"xyz","status":"verified"}]}\n-->'
        self.assertEqual(github.parse_verdicts(bad), [])

    def test_failure_log_cannot_smuggle_a_verdict_block(self):
        forged = github.verdict_block([{'track': 'full', 'commit': 'b' * 40, 'status': 'verified',
                                        'sigma': 1, 'hverify': 1, 'score': '1'}])
        with self.sessions() as session:
            sub = Submission(user_id=self.user_id, track='full', status='rejected',
                             commit='c' * 40, source_repo='https://github.com/author/repo.git',
                             pr_number=7, pr_url='https://github.com/owner/repo/pull/7',
                             detail=json.dumps({'contract': contract.contract_id(),
                                                'failure': {'message': 'error: \n' + forged + '\n'}}))
            session.add(sub)
            schedule_report(session, sub)
            session.commit()
        with patch.object(settings, 'github_token', 'test'), patch('app.worker.github.post_status'), \
             patch('app.worker.github.post_comment', return_value=9) as post:
            worker.deliver_report(sub.id)
        body = post.call_args.args[2]
        self.assertEqual([(v['commit'], v['status']) for v in github.parse_verdicts(body)],
                         [('c' * 40, 'rejected')])
        self.assertEqual(github.parse_verdicts(forged + '\n\nDetails: https://sig.golf'), [])

    def test_resync_merges_edited_comments_and_preserves_other_heads(self):
        def entry(commit, status, at):
            value = {'track': 'full', 'commit': commit * 40, 'status': status, 'finished_at': at,
                     'contract': contract.contract_id()}
            if status == 'verified':
                value.update(sigma=2274, hverify=160, score='363840')
            return value
        failed = entry('a', 'failed', '2026-09-10T10:00:00Z')
        retry = entry('a', 'verified', '2026-09-10T11:00:00Z')
        other = entry('b', 'rejected', '2026-09-10T10:30:00Z')
        comments = [
            {'id': 1, 'user': {'login': 'sig-bot'}, 'updated_at': '2026-09-10T11:00:01Z',
             'body': github.verdict_block([retry])},
            {'id': 2, 'user': {'login': 'sig-bot'}, 'updated_at': '2026-09-10T10:30:01Z',
             'body': github.verdict_block([failed, other])},
            {'id': 3, 'user': {'login': 'mallory'}, 'body': github.verdict_block([failed])},
        ]
        for order in (comments, comments[::-1]):
            merged = {v['commit']: (v['status'], cid) for v, cid in resync.latest_verdicts(order, 'sig-bot')}
            self.assertEqual(merged, {'a' * 40: ('verified', 1), 'b' * 40: ('rejected', 2)})
        comments[1]['updated_at'] = '2026-09-10T12:00:00Z'
        self.assertEqual({v['commit']: v['status'] for v, _ in resync.latest_verdicts(comments, 'sig-bot')}
                         ['a' * 40], 'verified')

    def test_resync_rebuilds_submissions_records_and_notes_from_github(self):
        block = github.verdict_block([{'track': 'full', 'commit': 'a' * 40, 'status': 'verified',
                                       'sigma': 2274, 'hverify': 160, 'score': '363840',
                                       'duration_s': 300.0, 'finished_at': '2026-09-10T10:00:00Z',
                                       'contract': contract.contract_id(), 'record': True}])
        forged = github.verdict_block([{'track': 'full', 'commit': 'd' * 40, 'status': 'verified',
                                        'sigma': 1, 'hverify': 1, 'score': '1'}])
        pulls = [
            {'number': 7, 'state': 'closed', 'merged_at': None, 'created_at': '2026-09-09T00:00:00Z',
             'user': {'login': 'alice', 'id': 42}, 'body': 'Averaging over classes.\nAssisted by: Model X',
             'base': {'ref': 'main', 'repo': {'default_branch': 'main'}}, 'head': {'sha': 'a' * 40, 'repo': {'clone_url': 'https://github.com/alice/entries.git'}}},
            {'number': 8, 'state': 'open', 'merged_at': None, 'created_at': '2026-09-12T00:00:00Z',
             'user': {'login': 'bob', 'id': 43}, 'body': '', 'base': {'ref': 'main', 'repo': {'default_branch': 'main'}}, 'head': {'sha': 'b' * 40, 'repo': None}},
        ]
        comments = {7: [{'id': 55, 'user': {'login': 'sig-bot'}, 'body': 'verified\n\n' + block},
                        {'id': 56, 'user': {'login': 'mallory'}, 'body': forged}], 8: []}
        with patch.object(settings, 'github_token', 'test'), patch.object(settings, 'bot_login', 'sig-bot'), \
             patch('app.resync.SessionLocal', self.sessions), \
             patch('app.resync.github.list_pulls', return_value=pulls), \
             patch('app.resync.github.list_comments', side_effect=lambda repo, n: comments[n]), \
             patch('app.resync.github.read_file', return_value='## Idea\n\nAverage over classes.'), \
             patch('app.main.handle_pull_request') as queue:
            first = resync.resync()
            second = resync.resync()
        self.assertEqual(first, {'restored': 1, 'promoted': 1, 'queued': 1})
        self.assertEqual(second['restored'], 0)
        queue.assert_called_with('owner/repo', 8, 'b' * 40, announce=False)
        with self.sessions() as session:
            sub = session.get(Submission, legacy_pr_submission_id('owner/repo', 7, 'a' * 40))
            self.assertEqual((sub.sigma, sub.hverify, sub.score, sub.status, sub.is_record, sub.user.login),
                             (2274, 160, '363840', 'verified', True, 'alice'))
            self.assertEqual(sub.record_at.strftime('%Y-%m-%d %H:%M'), '2026-09-10 10:00')
            self.assertEqual(sub.assisted_by, 'Model X')
            self.assertEqual(sub.notes, '## Idea\n\nAverage over classes.')
            self.assertEqual(sub.detail_dict['github_comment_id'], 55)
            self.assertIsNone(session.scalars(select(Submission).where(Submission.commit == 'd' * 40)).first())

    def test_resync_decides_records_in_verification_finish_order(self):
        # (PR, commit, sigma, hverify, finished_at, original bot record flag for legacy timestamp ties)
        heads = [(5, 'e' * 40, 1900, 200, '2026-09-12T00:00:00Z', True),    # a later copy of the record
                 (6, 'a' * 40, 2000, 200, '2026-09-10T00:00:00Z', False),   # improves 2100 x 200
                 (8, 'c' * 40, 1900, 200, '2026-09-11T00:00:00Z', True),    # same second as #7: keep the recorded winner
                 (7, 'b' * 40, 1900, 200, '2026-09-11T00:00:00Z', False),
                 (9, 'd' * 40, 2100, 200, '2026-09-09T00:00:00Z', True)]    # the track's first verified head
        pulls, comments = [], {}
        for number, commit, sigma, hverify, finished, flag in heads:
            pulls.append({'number': number, 'state': 'closed', 'merged_at': None,
                          'created_at': '2026-09-01T00:00:00Z', 'user': {'login': 'alice', 'id': 42}, 'body': '',
                          'base': {'ref': 'main', 'repo': {'default_branch': 'main'}},
                          'head': {'sha': commit, 'repo': None}})
            block = github.verdict_block([{'track': 'full', 'commit': commit, 'status': 'verified',
                                           'sigma': sigma, 'hverify': hverify, 'score': str(sigma * hverify),
                                           'finished_at': finished, 'record': flag, 'contract': contract.contract_id()}])
            comments[number] = [{'id': number, 'user': {'login': 'sig-bot'}, 'body': block}]
        with patch.object(settings, 'github_token', 'test'), patch.object(settings, 'bot_login', 'sig-bot'), \
             patch('app.resync.SessionLocal', self.sessions), \
             patch('app.resync.github.list_pulls', return_value=pulls), \
             patch('app.resync.github.list_comments', side_effect=lambda repo, n: comments[n]), \
             patch('app.resync.github.read_file', return_value=None):
            self.assertEqual(resync.resync(), {'restored': 5, 'promoted': 3, 'queued': 0})
        with self.sessions() as session:
            record = {n: session.get(Submission, legacy_pr_submission_id('owner/repo', n, c)).is_record
                      for n, c, *_ in heads}
            self.assertEqual(record, {5: False, 6: True, 7: False, 8: True, 9: True})
            self.assertEqual(records.current_record(session, 'full').pr_number, 8)
            self.assertEqual([s.pr_number for s in records.frontier(session, 'full')], [8, 6, 9])

    def test_replay_preserves_multiple_legacy_improvements_in_one_second(self):
        at = utcnow().replace(microsecond=0)
        ids = []
        with self.sessions() as session:
            for pr, sigma in zip((9, 7), (2000, 1900)):
                sub = Submission(user_id=self.user_id, track='full', sigma=sigma, hverify=200,
                    score=str(sigma * 200), status='verified',
                    source_repo='https://github.com/a/b.git', commit=str(pr) * 40,
                    pr_number=pr, pr_url=f'https://github.com/owner/repo/pull/{pr}', finished_at=at,
                    detail=json.dumps({'contract': contract.contract_id(), 'recorded_record': True}))
                session.add(sub)
                session.flush()
                ids.append(sub.id)
            session.commit()
        with patch('app.resync.SessionLocal', self.sessions):
            self.assertEqual(resync.replay_records(), 2)
            self.assertEqual(resync.replay_records(), 0)
        with self.sessions() as session:
            self.assertTrue(all(session.get(Submission, sid).is_record for sid in ids))
            self.assertEqual(records.current_record(session, 'full').sigma, 1900)
            self.assertEqual([p['value'] for p in records.curve(session, 'full')], [400000, 380000])

    def test_github_receives_only_statuses_and_comments(self):
        """Queue, verify, report, re-report and rebuild through the real GitHub client: nothing but commit
        statuses and the verdict comment is ever written, and nothing is merged or closed."""
        head = 'b' * 40
        pr = {'number': 9, 'state': 'open', 'changed_files': 1, 'body': 'A proof.', 'merged_at': None,
              'user': {'login': 'alice', 'id': 42}, 'created_at': '2026-09-01T00:00:00Z',
              'base': {'ref': 'main', 'repo': {'default_branch': 'main'}},
              'head': {'sha': head, 'repo': {'clone_url': 'https://github.com/alice/entries.git'}}}
        calls, comment = [], {}

        def respond(request):
            method, path = request.method, request.url.path
            calls.append((method, path))
            if method == 'GET' and path == '/repos/owner/repo/pulls/9':
                return httpx.Response(200, json=pr)
            if method == 'GET' and path == '/repos/owner/repo/pulls/9/files':
                return httpx.Response(200, json=[{'filename': f'{ROOT}/Solution.lean'}])
            if method == 'GET' and path == '/repos/owner/repo/pulls':
                return httpx.Response(200, json=[pr])
            if method == 'GET' and path == '/repos/owner/repo/issues/9/comments':
                return httpx.Response(200, json=[comment] if comment else [])
            if method == 'POST' and path == f'/repos/owner/repo/statuses/{head}':
                return httpx.Response(201, json={})
            if method == 'POST' and path == '/repos/owner/repo/issues/9/comments':
                comment.update(id=77, user={'login': 'sig-bot'}, body=json.loads(request.content)['body'])
                return httpx.Response(201, json={'id': 77})
            if method == 'PATCH' and path == '/repos/owner/repo/issues/comments/77':
                comment['body'] = json.loads(request.content)['body']
                return httpx.Response(200, json={})
            return httpx.Response(404, json={})

        real_client = httpx.Client
        client = lambda **kw: real_client(transport=httpx.MockTransport(respond), **kw)
        with patch.object(settings, 'github_token', 'test'), patch.object(settings, 'bot_login', 'sig-bot'), \
             patch('app.github.httpx.Client', side_effect=client), patch('app.resync.SessionLocal', self.sessions):
            queued = main.handle_pull_request('owner/repo', 9, head)
            with self.sessions() as session:
                sub = session.get(Submission, queued['id'])
            self.assertTrue(self.verify(sub).is_record)
            worker.deliver_report(sub.id)
            with self.sessions() as session:
                schedule_report(session, session.get(Submission, sub.id))
                session.commit()
            worker.deliver_report(sub.id)
            resync.resync()
        self.assertIn('new record', comment['body'])
        self.assertIn(('PATCH', '/repos/owner/repo/issues/comments/77'), calls)
        writes = {(m, p) for m, p in calls if m != 'GET'}
        self.assertEqual(writes, {('POST', f'/repos/owner/repo/statuses/{head}'),
                                  ('POST', '/repos/owner/repo/issues/9/comments'),
                                  ('PATCH', '/repos/owner/repo/issues/comments/77')})
        self.assertFalse(any(m in ('PUT', 'DELETE') or 'merge' in p for m, p in calls))

    def test_startup_refreshes_the_phony_board_only_in_phony_mode(self):
        with patch.object(settings, 'phony', True), patch('app.main.SessionLocal', self.sessions), \
             patch('seed_demo.refresh', return_value=3) as refresh:
            main.prepare_board()
        refresh.assert_called_once()
        with patch.object(settings, 'phony', False), patch('app.main.SessionLocal', self.sessions), \
             patch('seed_demo.refresh') as refresh:
            main.prepare_board()
        refresh.assert_not_called()
        with self.sessions() as session:
            self.assertEqual(session.scalars(select(Submission)).all(), [])

    def test_reports_never_retarget_an_old_core_pr(self):
        sub = self.submission()
        sub.pr_url = 'https://github.com/owner/core/pull/7'
        with patch('app.worker.github.post_status') as status, patch('app.worker.github.post_comment') as post:
            with self.assertRaises(ValueError):
                worker.report(sub)
            status.assert_not_called()
            post.assert_not_called()

    def test_old_repository_outbox_does_not_block_current_reports(self):
        for n in range(25):
            sub = self.submission(pr=n + 100)
            with self.sessions() as session:
                old = session.get(Submission, sub.id)
                old.pr_url = f'https://github.com/owner/core/pull/{old.pr_number}'
                schedule_report(session, old)
                session.commit()
        current = self.submission()
        with self.sessions() as session:
            schedule_report(session, session.get(Submission, current.id))
            session.commit()
        with patch.object(settings, 'github_token', 'test'), patch('app.worker.report', return_value=456) as report:
            worker.deliver_report(sub.id)
            report.assert_not_called()
            worker.retry_reports()
            report.assert_called_once()
            self.assertEqual(report.call_args.args[0].id, current.id)
        with self.sessions() as session:
            self.assertIsNotNone(session.get(GithubReport, sub.id))
            self.assertIsNone(session.get(GithubReport, current.id))

    def test_pr_identity_requires_a_matching_github_pull_request_url(self):
        sub = self.submission()
        for url in ('https://example.com/owner/repo/pull/7', 'https://github.com/owner/repo/pull/8',
                    'https://github.com/owner/repo/pull/7/extra', None):
            sub.pr_url = url
            self.assertIsNone(sub.pr_repository)

    def test_deleted_result_comment_is_recreated(self):
        sub = self.submission()
        sub.detail = json.dumps({'github_comment_id': 123, 'contract': contract.contract_id()})
        response = httpx.Response(404, request=httpx.Request('PATCH', 'https://api.github.com/comment'))
        error = httpx.HTTPStatusError('deleted', request=response.request, response=response)
        with patch('app.worker.github.post_status'), patch('app.worker.github.update_comment', side_effect=error), \
             patch('app.worker.github.post_comment', return_value=456) as post:
            self.assertEqual(worker.report(sub), 456)
            post.assert_called_once()

    def test_production_worker_refuses_web_role_even_if_settings_loaded(self):
        with patch.object(settings, 'environment', 'production'), patch.object(settings, 'role', 'web'), \
             patch('app.worker.init_db') as initialize:
            with self.assertRaises(SystemExit):
                worker.main()
            initialize.assert_not_called()

    def test_worker_lock_excludes_another_worker_and_is_released(self):
        with local_lock('worker', blocking=False):
            with self.assertRaises(BlockingIOError):
                with local_lock('worker', blocking=False):
                    self.fail('second worker acquired the active lock')
        with local_lock('worker', blocking=False):
            pass

    def pipeline(self, sub, result, *, returncode=0):
        proc = Mock(returncode=returncode)
        proc.communicate.return_value = (json.dumps(result), '')
        with patch('app.worker.subprocess.Popen', return_value=proc) as launch:
            result, log_path = worker.run_pipeline(sub)
            self.assertTrue(launch.call_args.kwargs['start_new_session'])
            self.assertTrue(Path(log_path).is_file())
            return result

    def test_pipeline_uses_the_contract_time_limit(self):
        sub = self.submission()
        limit = contract.load()['limits']['wall_clock_seconds']
        proc = Mock(returncode=0)
        proc.communicate.return_value = (json.dumps({'status': 'rejected'}), '')
        with patch('app.worker.subprocess.Popen', return_value=proc), \
                patch('app.worker.source_archive.recover_metadata', return_value={}):
            result, _ = worker.run_pipeline(sub)
        self.assertEqual(result['status'], 'rejected')
        proc.communicate.assert_called_once_with(timeout=limit + 600)

    def test_pipeline_rejects_forged_or_inconsistent_success_metadata(self):
        sub = self.submission()
        valid = self.result(sub)
        self.assertEqual(self.pipeline(sub, valid)['status'], 'failed')  # no durable source
        metadata = self.retain_source(sub)
        self.assertEqual(self.pipeline(sub, valid)['source_archive'], metadata)
        self.assertEqual(self.pipeline(sub, valid)['status'], 'verified')
        for changes in ({'track': 'no-such-track'}, {'sigma': True}, {'sigma': -1}, {'score': '1'}, {'score': 363840},
                        {'hverify': 0}, {'commit': 'b' * 40}, {'sigma': None},
                        {'sigma': 2 ** 62 + 1, 'score': str((2 ** 62 + 1) * 160)}):
            self.assertEqual(self.pipeline(sub, valid | changes)['status'], 'failed', changes)
        self.assertEqual(self.pipeline(sub, valid, returncode=1)['status'], 'failed')
        self.assertEqual(self.pipeline(sub, [])['status'], 'failed')
        self.assertEqual(self.pipeline(sub, {'status': 'rejected', 'reason': 'no'})['status'], 'rejected')
        self.assertEqual(self.pipeline(sub, {'status': 'policy_rejected', 'errors': ['flat root required']})['status'],
                         'policy_rejected')

    def test_pipeline_outer_timeout_stops_group_and_preserves_log(self):
        sub = self.submission()
        metadata = self.retain_source(sub)
        proc = Mock(pid=12345, returncode=-15)
        proc.communicate.side_effect = [subprocess.TimeoutExpired('verify', 1), ('partial output', '')]
        with patch('app.worker.subprocess.Popen', return_value=proc), patch('app.worker.os.killpg') as kill:
            result, log_path = worker.run_pipeline(sub)
        kill.assert_called_once_with(12345, worker.signal.SIGTERM)
        self.assertEqual(result['status'], 'timeout')
        self.assertEqual(result['source_archive'], metadata)
        self.assertIn('partial output', Path(log_path).read_text())
        self.assertIn('outer time limit', Path(log_path).read_text())

    def test_source_archive_survives_source_changes_and_missing_archive_is_explicit(self):
        import hashlib
        sub = self.submission(sigma=None, hverify=None, status='pending')
        metadata = self.retain_source(sub)
        with patch('app.worker.run_pipeline', return_value=(self.result(sub, source_archive=metadata), None)):
            worker.process(sub.id)
        (self.data / ('input-' + sub.id) / 'Solution.lean').write_text('-- replaced after force-push')
        with self.sessions() as session:
            checked = session.get(Submission, sub.id)
            self.assertEqual(worker.verdict_entry(checked)['source_archive'], metadata)
            self.assertNotIn('pull/7/head', checked.fetch_command)
            main.app.dependency_overrides[main.get_session] = lambda: session
            try:
                with TestClient(main.app) as client:
                    response = client.get(f'/submissions/{sub.id}/source.zip')
                    self.assertEqual(response.status_code, 200)
                    self.assertEqual(hashlib.sha256(response.content).hexdigest(), metadata['sha256'])
                    self.assertIn('Download exact source ZIP', client.get(f'/submissions/{sub.id}').text)
                    source_archive.validated_path(checked).unlink()
                    self.assertEqual(client.get(f'/submissions/{sub.id}/source.zip').status_code, 404)
                    self.assertIn('Source archive unavailable.', client.get(f'/submissions/{sub.id}').text)
                    self.assertEqual(checked.status, 'verified')
            finally:
                main.app.dependency_overrides.clear()

    def test_resync_retains_archive_identity_even_when_archive_bytes_are_missing(self):
        sub = self.submission()
        meta = self.retain_source(sub)
        sub.finished_at = utcnow()
        sub.detail = json.dumps({'contract': contract.contract_id(), 'source_archive': meta})
        result = worker.verdict_entry(sub)
        source_archive.validated_path(sub).unlink()
        with self.sessions() as session:
            session.delete(session.get(Submission, sub.id))
            session.commit()
        pulls = [{'number': 7, 'state': 'closed', 'user': {'login': 'proof-author'},
                  'head': {'sha': sub.commit, 'repo': None}}]
        comments = [{'id': 1, 'user': {'login': 'sig-bot'}, 'body': github.verdict_block([result])}]
        with patch.object(settings, 'github_token', 'test'), patch.object(settings, 'bot_login', 'sig-bot'), \
             patch('app.resync.SessionLocal', self.sessions), \
             patch('app.resync.github.list_pulls', return_value=pulls), \
             patch('app.resync.github.list_comments', return_value=comments), \
             patch('app.resync.github.read_file', return_value=None):
            self.assertEqual(resync.resync()['restored'], 1)
        with self.sessions() as session:
            restored = session.get(Submission, sub.id)
            self.assertEqual(restored.detail_dict['source_archive'], meta)
            self.assertEqual((restored.status, restored.sigma, restored.score), ('verified', 2274, '363840'))
            self.assertIsNone(restored.archive_url)

    def test_pipeline_termination_escalates_if_graceful_shutdown_stalls(self):
        proc = Mock(pid=12345)
        proc.communicate.side_effect = [subprocess.TimeoutExpired('verify', 40), ('stopped', '')]
        with patch('app.worker.os.killpg') as kill:
            self.assertEqual(worker._stop_pipeline(proc), ('stopped', ''))
        self.assertEqual([call.args for call in kill.call_args_list],
                         [(12345, worker.signal.SIGTERM), (12345, worker.signal.SIGKILL)])

    def test_github_http_failure_is_not_silently_treated_as_reported(self):
        response = httpx.Response(503, request=httpx.Request('POST', 'https://api.github.com/test'), text='unavailable')
        with self.assertRaises(httpx.HTTPStatusError):
            worker.github._check(response, 'test status')


if __name__ == '__main__':
    unittest.main()
