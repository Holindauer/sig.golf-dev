"""Small GitHub client and atomic beta-branch record publisher."""
from __future__ import annotations

import base64
import json
import re
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

from presentation import PresentationError, validate_json, validate_svg, MAX_PRESENTATION_BYTES

REPO = 'leanEthereum/sig.golf-submissions'
BRANCH = 'beta'
SHA = re.compile(r'[0-9a-f]{40}|[0-9a-f]{64}')
LOGIN = re.compile(r'[A-Za-z0-9-]{1,39}')
MAX_REGISTRY = 1024 * 1024


class GithubError(RuntimeError):
    def __init__(self, message: str, status: int | None = None):
        super().__init__(message)
        self.status = status


class Github:
    def __init__(self, token: str):
        if not token.strip():
            raise GithubError('GitHub token is missing')
        self.token = token.strip()

    def request(self, method: str, path: str, body: dict | None = None) -> dict | list:
        data = json.dumps(body, separators=(',', ':')).encode() if body is not None else None
        request = urllib.request.Request('https://api.github.com' + path, data=data, method=method,
            headers={'Accept': 'application/vnd.github+json', 'Authorization': 'Bearer ' + self.token,
                     'X-GitHub-Api-Version': '2022-11-28', 'User-Agent': 'sig-golf-beta-bot',
                     **({'Content-Type': 'application/json'} if data is not None else {})})
        try:
            with urllib.request.urlopen(request, timeout=30) as response:
                payload = response.read(MAX_REGISTRY + 1024)
                if len(payload) > MAX_REGISTRY + 512:
                    raise GithubError('GitHub response exceeded its limit')
                value = json.loads(payload)
                if not isinstance(value, (dict, list)):
                    raise GithubError('GitHub returned invalid JSON')
                return value
        except urllib.error.HTTPError as exc:
            raise GithubError(f'GitHub {method} {path} returned {exc.code}', exc.code) from exc
        except (urllib.error.URLError, json.JSONDecodeError) as exc:
            raise GithubError(f'GitHub request failed: {exc}') from exc

    def get(self, path: str) -> dict | list:
        return self.request('GET', path)

    def post(self, path: str, body: dict) -> dict:
        value = self.request('POST', path, body)
        if not isinstance(value, dict):
            raise GithubError('GitHub returned a non-object')
        return value

    def status(self, commit: str, state: str, description: str, context: str) -> None:
        if not SHA.fullmatch(commit) or state not in {'pending', 'success', 'failure', 'error'}:
            raise GithubError('invalid status')
        self.post(f'/repos/{REPO}/statuses/{commit}',
                  {'state': state, 'context': context, 'description': description[:140],
                   'target_url': f'https://beta.sig.golf/site/'})

    def _pr_root_items(self, commit: str) -> list[dict]:
        info = self.get(f'/repos/{REPO}/git/commits/{commit}')
        tree = info.get('tree', {}).get('sha') if isinstance(info, dict) else None
        if not isinstance(tree, str) or not SHA.fullmatch(tree):
            raise GithubError('GitHub did not return the PR tree')
        listing = self.get(f'/repos/{REPO}/git/trees/{tree}')
        if not isinstance(listing, dict) or listing.get('truncated') is not False:
            raise GithubError('GitHub returned an incomplete PR tree')
        return listing.get('tree', [])

    def source_tree(self, commit: str) -> str:
        items = [item for item in self._pr_root_items(commit) if item.get('path') == 'submission']
        if len(items) != 1 or items[0].get('type') != 'tree' or not SHA.fullmatch(items[0].get('sha', '')):
            raise GithubError('PR has no submission tree')
        return items[0]['sha']

    def presentation_tree(self, commit: str, claim: dict) -> str | None:
        """Return a validated optional tree, or ignore malformed display-only files."""
        roots = [item for item in self._pr_root_items(commit) if item.get('path') == 'presentation']
        if not roots:
            return None
        try:
            if len(roots) != 1 or roots[0].get('type') != 'tree' or not SHA.fullmatch(roots[0].get('sha', '')):
                raise PresentationError('presentation must be a directory')
            tree = roots[0]['sha']
            listing = self.get(f'/repos/{REPO}/git/trees/{tree}')
            if not isinstance(listing, dict) or listing.get('truncated') is not False:
                raise PresentationError('incomplete presentation tree')
            files = listing.get('tree', [])
            if not isinstance(files, list) or not 1 <= len(files) <= 2:
                raise PresentationError('presentation needs presentation.json and optional scheme.svg')
            entries = {item.get('path'): item for item in files}
            if set(entries) - {'presentation.json', 'scheme.svg'} or 'presentation.json' not in entries:
                raise PresentationError('presentation contains unknown files')
            for name, item in entries.items():
                if (item.get('type') != 'blob' or item.get('mode') not in {'100644', '100755'} or not SHA.fullmatch(item.get('sha', '')) or
                        type(item.get('size')) is not int or not 0 <= item['size'] <= MAX_PRESENTATION_BYTES):
                    raise PresentationError(f'{name} is not a bounded regular file')
            def blob(name: str) -> bytes:
                response = self.get(f'/repos/{REPO}/git/blobs/{entries[name]["sha"]}')
                if not isinstance(response, dict) or response.get('encoding') != 'base64':
                    raise PresentationError(f'{name} has invalid blob encoding')
                try:
                    data = base64.b64decode(''.join(response['content'].split()), validate=True)
                except (KeyError, ValueError, TypeError, AttributeError) as exc:
                    raise PresentationError(f'{name} is not base64') from exc
                if len(data) != entries[name]['size']:
                    raise PresentationError(f'{name} blob size changed')
                return data
            metadata = validate_json(blob('presentation.json'), claim)
            if metadata.get('diagram', False) != ('scheme.svg' in entries):
                raise PresentationError('diagram flag must match scheme.svg')
            if 'scheme.svg' in entries:
                validate_svg(blob('scheme.svg'))
            return tree
        except PresentationError as exc:
            print(f'Ignoring invalid optional presentation at {commit}: {exc}', flush=True)
            return None



def registry_from_branch(api: Github) -> dict:
    path = f'/repos/{REPO}/contents/records.json?ref={BRANCH}'
    try:
        value = api.get(path)
    except GithubError as exc:
        if exc.status == 404:
            return {'version': 1, 'submissions': []}
        raise
    if not isinstance(value, dict) or value.get('encoding') != 'base64':
        raise GithubError('invalid records.json response')
    try:
        raw = base64.b64decode(''.join(value['content'].split()), validate=True)
        if len(raw) > MAX_REGISTRY:
            raise ValueError('too large')
        registry = json.loads(raw)
    except (KeyError, ValueError, TypeError, AttributeError) as exc:
        raise GithubError('invalid records.json') from exc
    if (not isinstance(registry, dict) or registry.get('version') != 1 or
            not isinstance(registry.get('submissions'), list)):
        raise GithubError('unsupported records.json schema')
    return registry


def _entry(pr: dict, result: dict, contract: str, tree: str) -> dict:
    commit = pr.get('head', {}).get('sha')
    author = pr.get('user', {}).get('login')
    number = pr.get('number')
    claim = result.get('claim')
    if (not isinstance(commit, str) or not SHA.fullmatch(commit) or
            not isinstance(contract, str) or not SHA.fullmatch(contract) or
            not isinstance(tree, str) or not SHA.fullmatch(tree) or
            type(number) is not int or number < 1 or
            not isinstance(author, str) or not LOGIN.fullmatch(author) or
            not isinstance(claim, dict) or set(claim) != {'S', 'W', 'C'} or
            any(type(claim[k]) is not int or claim[k] < 0 for k in claim)):
        raise GithubError('invalid verified result identity')
    body = pr.get('body') or ''
    match = re.search(r'(?im)^Assisted by:\s*(.{1,80})$', body)
    assistant = match.group(1).strip() if match else None
    return {'id': commit + ':' + contract[:12], 'commit': commit,
            'contract_commit': contract, 'pr': number,
            'pr_url': f'https://github.com/{REPO}/pull/{number}',
            'author': author, 'avatar_url': f'https://github.com/{author}.png?size=64',
            'assisted_by': assistant, 'title': str(pr.get('title') or '')[:120],
            'verified_at': datetime.now(timezone.utc).isoformat(timespec='seconds').replace('+00:00', 'Z'),
            'S': claim['S'], 'W': claim['W'], 'C': claim['C'],
            'score': str(claim['S'] * claim['C']), 'source_tree': tree,
            'source_path': f'verified/{commit}'}


def publish_verified(api: Github, pr: dict, result: dict, contract: str,
                     local_records: Path | None = None) -> tuple[dict, bool]:
    """Publish a checked result and its source tree by non-forced CAS on beta.

    All verified PRs enter the registry; an improvement is marked as a record. Retrying an
    already published result is idempotent. No success status should precede this call.
    """
    if result.get('status') != 'verified' or pr.get('base', {}).get('ref') != BRANCH:
        raise GithubError('only a verified beta PR can be published')
    commit = pr.get('head', {}).get('sha')
    if not isinstance(commit, str) or not SHA.fullmatch(commit):
        raise GithubError('invalid PR head')
    fresh = api.get(f'/repos/{REPO}/pulls/{pr["number"]}')
    if not isinstance(fresh, dict) or fresh.get('head', {}).get('sha') != commit:
        raise GithubError('PR head changed after verification')
    tree = api.source_tree(commit)
    presentation = api.presentation_tree(commit, result["claim"])
    candidate = _entry(pr, result, contract, tree)
    if presentation is not None:
        candidate["presentation"] = True
    for _ in range(3):
        ref = api.get(f'/repos/{REPO}/git/ref/heads/{BRANCH}')
        head = ref.get('object', {}).get('sha') if isinstance(ref, dict) else None
        if not isinstance(head, str) or not SHA.fullmatch(head):
            raise GithubError('invalid beta ref')
        current = registry_from_branch(api)
        existing = next((item for item in current['submissions'] if item.get('id') == candidate['id']), None)
        if existing is not None:
            if any(existing.get(key) != candidate[key] for key in ('commit', 'contract_commit', 'S', 'W', 'C', 'score', 'source_tree')):
                raise GithubError('published result conflicts with verified result')
            if local_records is not None:
                write_local_registry(local_records, current)
            return existing, False
        prior = [int(item['score']) for item in current['submissions']
                 if item.get('contract_commit') == contract and isinstance(item.get('score'), str)
                 and re.fullmatch(r'0|[1-9][0-9]*', item['score'])]
        candidate['record'] = not prior or int(candidate['score']) < min(prior)
        updated = {'version': 1, 'submissions': [*current['submissions'], candidate]}
        raw = (json.dumps(updated, sort_keys=True, separators=(',', ':')) + '\n').encode()
        if len(raw) > MAX_REGISTRY:
            raise GithubError('records.json reached its size limit')
        base_commit = api.get(f'/repos/{REPO}/git/commits/{head}')
        base_tree = base_commit.get('tree', {}).get('sha') if isinstance(base_commit, dict) else None
        if not isinstance(base_tree, str) or not SHA.fullmatch(base_tree):
            raise GithubError('invalid beta commit tree')
        blob = api.post(f'/repos/{REPO}/git/blobs', {'content': raw.decode(), 'encoding': 'utf-8'})
        if not SHA.fullmatch(blob.get('sha', '')):
            raise GithubError('invalid record blob')
        snapshot_tree = tree
        if presentation is not None:
            combined = api.post(f'/repos/{REPO}/git/trees', {'base_tree': tree, 'tree': [
                {'path': 'presentation', 'mode': '040000', 'type': 'tree', 'sha': presentation}]})
            snapshot_tree = combined.get('sha', '')
            if not SHA.fullmatch(snapshot_tree):
                raise GithubError('invalid presentation snapshot tree')
        new_tree = api.post(f'/repos/{REPO}/git/trees', {'base_tree': base_tree, 'tree': [
            {'path': 'records.json', 'mode': '100644', 'type': 'blob', 'sha': blob['sha']},
            {'path': candidate['source_path'], 'mode': '040000', 'type': 'tree', 'sha': snapshot_tree}]})
        if not SHA.fullmatch(new_tree.get('sha', '')):
            raise GithubError('invalid publication tree')
        message = f"Verify PR #{pr['number']}: {candidate['score']} (beta)"
        commit_obj = api.post(f'/repos/{REPO}/git/commits',
                              {'message': message, 'tree': new_tree['sha'], 'parents': [head]})
        if not SHA.fullmatch(commit_obj.get('sha', '')):
            raise GithubError('invalid publication commit')
        try:
            api.request('PATCH', f'/repos/{REPO}/git/refs/heads/{BRANCH}',
                        {'sha': commit_obj['sha'], 'force': False})
        except GithubError as exc:
            if exc.status in {409, 422}:
                continue
            raise
        if local_records is not None:
            write_local_registry(local_records, updated)
        return candidate, True
    raise GithubError('beta changed too often to publish this result')


def write_local_registry(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix('.tmp')
    temporary.write_text(json.dumps(value, sort_keys=True, separators=(',', ':')) + '\n')
    temporary.replace(path)
