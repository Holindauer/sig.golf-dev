'use strict';

const page = document.body.dataset.page;
const query = new URLSearchParams(location.search);
const byId = id => document.getElementById(id);
function showMissing(label) {
  document.querySelector('main').replaceChildren();
  const title = document.createElement('h1');
  title.textContent = label + ' not found';
  const back = document.createElement('a');
  back.href = '/site/#leaderboard';
  back.textContent = '← Back to leaderboard';
  document.querySelector('main').append(title, back);
}
if (page === 'submission') {
  const entry = previewScores.find(item => item.id === query.get('id'));
  if (!entry) {
    showMissing('Submission');
  } else {
    document.title = entry.name + ' · sig.golf';
    byId('detail-title').textContent = entry.name;
    byId('detail-avatar').appendChild(previewAvatar(entry.profile, 'profile-avatar'));
    const solver = byId('detail-solver');
    solver.textContent = entry.profile.login;
    solver.href = previewSolverUrl(entry.profile);
    if (entry.assistant) {
      byId('detail-assistant').hidden = false;
      byId('detail-assistant').textContent = entry.assistant;
      byId('detail-assisted').textContent = entry.assistant;
    } else {
      byId('detail-assisted-row').hidden = true;
    }
    byId('detail-score').textContent = previewFormat(entry.score);
    byId('detail-signature').textContent = previewFormat(entry.signature) + ' B';
    byId('detail-cycles').textContent = previewFormat(entry.cycles);
    byId('detail-id').textContent = '#' + entry.id;
    byId('detail-date').textContent = previewDate(entry.date);
    byId('detail-record').textContent = entry.record ? 'Yes' : 'No';
  }
} else if (page === 'solver') {
  const profile = previewProfiles.find(item => item.login === query.get('user'));
  if (!profile) {
    showMissing('Solver');
  } else {
    const entries = previewScores.filter(item => item.profile === profile)
      .sort((a, b) => a.score - b.score);
    document.title = profile.login + ' · sig.golf';
    byId('solver-name').textContent = profile.login;
    byId('solver-avatar').appendChild(previewAvatar(profile, 'profile-avatar'));
    byId('solver-count').textContent = String(entries.length);
    byId('solver-best').textContent = previewFormat(entries[0].score);
    const body = byId('solver-submissions');
    for (const entry of entries) {
      const row = document.createElement('tr');
      row.className = 'lb-row';
      row.addEventListener('click', event => {
        if (!event.target.closest('a')) location.href = previewSubmissionUrl(entry);
      });
      const name = document.createElement('td');
      const link = document.createElement('a');
      link.href = previewSubmissionUrl(entry);
      link.textContent = entry.name;
      name.appendChild(link);
      row.appendChild(name);
      for (const value of [
        previewFormat(entry.score), previewFormat(entry.signature) + ' B',
        previewFormat(entry.cycles), previewDate(entry.date)
      ]) {
        const cell = document.createElement('td');
        cell.className = 'number';
        cell.textContent = value;
        row.appendChild(cell);
      }
      body.appendChild(row);
    }
  }
}
