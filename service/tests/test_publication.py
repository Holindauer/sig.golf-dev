import base64
import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from github import GithubError, publish_verified

CONTRACT = 'a' * 40


def pr(number, sha):
    return {'number': number, 'head': {'sha': sha}, 'base': {'ref': 'beta'},
            'user': {'login': 'alice'}, 'body': 'Assisted by: Codex', 'title': f'Entry {number}'}


def result(s, c):
    return {'status': 'verified', 'claim': {'S': s, 'W': s, 'C': c,
            'layout': {'message': 0, 'secret_key': 32, 'public_key': 64,
                       'cache': 96, 'signature': 131168, 'witness': 131168 + s}}}


class FakeGithub:
    def __init__(self):
        self.head = '1' * 40
        self.registry = {'version': 1, 'submissions': []}
        self.prs = {}
        self.blob_content = None
        self.updates = 0
        self.conflict_once = False
        self.presentation = None

    def source_tree(self, commit):
        return '2' * 40

    def presentation_tree(self, commit, claim):
        return self.presentation

    def get(self, path):
        if '/pulls/' in path:
            return self.prs[int(path.rsplit('/', 1)[1])]
        if '/git/ref/heads/beta' in path:
            return {'object': {'sha': self.head}}
        if '/contents/records.json' in path:
            import json
            raw = json.dumps(self.registry).encode()
            return {'encoding': 'base64', 'content': base64.b64encode(raw).decode()}
        if '/git/commits/' in path:
            return {'tree': {'sha': '3' * 40}}
        raise AssertionError(path)

    def post(self, path, body):
        if path.endswith('/git/blobs'):
            self.blob_content = body['content']
            return {'sha': '4' * 40}
        if path.endswith('/git/trees'):
            if body['base_tree'] == '2' * 40:
                assert body['tree'] == [{'path': 'presentation', 'mode': '040000', 'type': 'tree', 'sha': self.presentation}]
                return {'sha': '7' * 40}
            assert body['tree'][1]['path'].startswith('verified/')
            assert body['tree'][1]['sha'] == ('7' * 40 if self.presentation else '2' * 40)
            return {'sha': '5' * 40}
        if path.endswith('/git/commits'):
            assert body['parents'] == [self.head]
            return {'sha': '6' * 40}
        raise AssertionError(path)

    def request(self, method, path, body):
        assert method == 'PATCH' and path.endswith('/git/refs/heads/beta')
        if self.conflict_once:
            self.conflict_once = False
            raise GithubError('race', 409)
        import json
        self.registry = json.loads(self.blob_content)
        self.head = body['sha']
        self.updates += 1
        return {}


class PublicationTests(unittest.TestCase):
    def test_record_nonrecord_and_idempotent_retry(self):
        api = FakeGithub()
        first = pr(1, 'b' * 40)
        api.prs[1] = first
        entry, changed = publish_verified(api, first, result(100, 200), CONTRACT)
        self.assertTrue(changed)
        self.assertTrue(entry['record'])
        self.assertEqual(entry['score'], '20000')
        self.assertEqual(entry['assisted_by'], 'Codex')
        again, changed = publish_verified(api, first, result(100, 200), CONTRACT)
        self.assertFalse(changed)
        self.assertEqual(again, entry)
        self.assertEqual(api.updates, 1)
        second = pr(2, 'c' * 40)
        api.prs[2] = second
        worse, _ = publish_verified(api, second, result(120, 200), CONTRACT)
        self.assertFalse(worse['record'])
        third = pr(3, 'd' * 40)
        api.prs[3] = third
        better, _ = publish_verified(api, third, result(80, 200), CONTRACT)
        self.assertTrue(better['record'])
        self.assertEqual(api.updates, 3)

    def test_optional_presentation_is_snapshotted_with_source(self):
        api = FakeGithub()
        api.presentation = '8' * 40
        item = pr(1, 'b' * 40)
        api.prs[1] = item
        entry, _ = publish_verified(api, item, result(100, 200), CONTRACT)
        self.assertTrue(entry['presentation'])
        self.assertEqual(api.updates, 1)

    def test_changed_pr_head_is_not_published(self):
        api = FakeGithub()
        old = pr(1, 'b' * 40)
        api.prs[1] = pr(1, 'c' * 40)
        with self.assertRaisesRegex(GithubError, 'changed'):
            publish_verified(api, old, result(100, 200), CONTRACT)
        self.assertEqual(api.updates, 0)

    def test_ref_conflict_retries_without_force(self):
        api = FakeGithub()
        item = pr(1, 'b' * 40)
        api.prs[1] = item
        api.conflict_once = True
        entry, changed = publish_verified(api, item, result(100, 200), CONTRACT)
        self.assertTrue(changed)
        self.assertTrue(entry['record'])
        self.assertEqual(api.updates, 1)


if __name__ == '__main__':
    unittest.main()
