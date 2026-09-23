'use strict';

const byId = id => document.getElementById(id);
const format = value => value.toLocaleString('en-US');
const url = item => '/site/submission.html?id=' + encodeURIComponent(item.id);
const dateLabel = value => new Date(value).toLocaleDateString('en-US', {
  month: 'short', day: 'numeric', year: 'numeric', timeZone: 'UTC'
});
function avatar(login, className = 'profile-avatar') {
  const img = document.createElement('img');
  img.className = className;
  img.src = `https://github.com/${encodeURIComponent(login)}.png?size=96`;
  img.alt = '';
  return img;
}
function missing(label) {
  document.querySelector('main').replaceChildren();
  const title = document.createElement('h1');
  title.textContent = label + ' not found';
  const back = document.createElement('a');
  back.href = '/site/#leaderboard';
  back.textContent = '← Back to leaderboard';
  document.querySelector('main').append(title, back);
}
async function load() {
  const [response, stateResponse] = await Promise.all([
    fetch('/site/records.json', {cache: 'no-store'}),
    fetch('/site/state.json', {cache: 'no-store'})
  ]);
  if (!response.ok || !stateResponse.ok) throw new Error('Cannot load verified records');
  const [value, state] = await Promise.all([response.json(), stateResponse.json()]);
  if (value.version !== 1 || !Array.isArray(value.submissions)) throw new Error('Invalid records');
  return value.submissions.filter(item => item.contract_commit === state.contract_commit);
}
async function render() {
  const records = await load();
  const query = new URLSearchParams(location.search);
  if (document.body.dataset.page === 'submission') {
    const entry = records.find(item => item.id === query.get('id'));
    if (!entry) return missing('Submission');
    document.title = `${entry.title || `PR #${entry.pr}`} · sig.golf`;
    byId('detail-title').textContent = entry.title || `PR #${entry.pr}`;
    byId('detail-avatar').appendChild(avatar(entry.author));
    byId('detail-solver').textContent = entry.author;
    byId('detail-solver').href = '/site/solver.html?user=' + encodeURIComponent(entry.author);
    if (entry.assisted_by) {
      byId('detail-assistant').hidden = false;
      byId('detail-assistant').textContent = entry.assisted_by;
      byId('detail-assisted').textContent = entry.assisted_by;
    } else byId('detail-assisted-row').hidden = true;
    byId('detail-score').textContent = format(BigInt(entry.score));
    byId('detail-signature').textContent = format(entry.S) + ' B';
    byId('detail-cycles').textContent = format(entry.C);
    byId('detail-witness').textContent = format(entry.W) + ' B';
    byId('detail-id').textContent = '#' + entry.pr + ' · ' + entry.commit.slice(0, 12);
    byId('detail-date').textContent = dateLabel(entry.verified_at);
    byId('detail-record').textContent = entry.record ? 'Yes' : 'No';
    byId('detail-pr').href = `https://github.com/leanEthereum/sig.golf-submissions/pull/${entry.pr}`;
    byId('detail-source').href = `https://github.com/leanEthereum/sig.golf-submissions/tree/beta/verified/${encodeURIComponent(entry.commit)}`;
  } else {
    const login = query.get('user');
    if (!login || !/^[A-Za-z0-9-]{1,39}$/.test(login)) return missing('Solver');
    const entries = records.filter(item => item.author.toLowerCase() === login.toLowerCase())
      .sort((a, b) => BigInt(a.score) < BigInt(b.score) ? -1 : BigInt(a.score) > BigInt(b.score) ? 1 : 0);
    if (!entries.length) return missing('Solver');
    document.title = `${login} · sig.golf`;
    byId('solver-name').textContent = login;
    byId('solver-avatar').appendChild(avatar(login));
    byId('solver-count').textContent = format(entries.length);
    byId('solver-best').textContent = format(BigInt(entries[0].score));
    const tbody = byId('solver-submissions');
    for (const entry of entries) {
      const row = document.createElement('tr');
      row.className = 'lb-row';
      const cells = [entry.title || `PR #${entry.pr}`, format(BigInt(entry.score)),
                     format(entry.S) + ' B', format(entry.C), dateLabel(entry.verified_at)];
      for (const [index, value] of cells.entries()) {
        const cell = document.createElement('td');
        if (index) cell.className = 'number';
        if (index === 0) {
          const link = document.createElement('a');
          link.href = url(entry);
          link.textContent = value;
          cell.appendChild(link);
        } else cell.textContent = value;
        row.appendChild(cell);
      }
      tbody.appendChild(row);
    }
  }
}
render().catch(() => missing('Verified record'));
