import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import bot


class ResetTests(unittest.TestCase):
    def test_old_verified_head_is_not_requeued_after_reset(self):
        old, fresh, contract = 'a' * 40, 'b' * 40, 'c' * 40
        class Api:
            def get(self, path):
                if path == '/user':
                    return {'login': 'bot'}
                raise AssertionError(path)
            def status(self, *args):
                pass
        registry = {'version': 1, 'submissions': [
            {'commit': old, 'contract_commit': 'd' * 40}]}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            with patch.object(bot.subprocess, 'run') as git, \
                 patch.object(bot, 'registry_from_branch', return_value=registry), \
                 patch.object(bot, 'open_prs', return_value=[
                     {'number': 1, 'head': {'sha': old}},
                     {'number': 2, 'head': {'sha': fresh}}]), \
                 patch.object(bot, 'checked_status', return_value=None), \
                 patch.object(bot, 'run_verifier', return_value={'status': 'rejected'}) as verify:
                git.return_value.stdout = contract + '\n'
                count = bot.once(Api(), root, root / 'records.json', root / 'state.json', root)
                self.assertEqual(count, 1)
                self.assertEqual(verify.call_args.args[0]['number'], 2)
                self.assertEqual(json.loads((root / 'records.json').read_text()), registry)
                self.assertEqual(json.loads((root / 'state.json').read_text())['contract_commit'], contract)


if __name__ == '__main__':
    unittest.main()
