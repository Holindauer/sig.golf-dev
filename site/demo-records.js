'use strict';

// Fictional preview data. Replace with verified GitHub submissions before launch.
const previewFamilies = [
  'Aster', 'Boreas', 'Cedar', 'Dorian', 'Echo', 'Fjord', 'Grove',
  'Helios', 'Iris', 'Juniper', 'Kite', 'Laurel', 'Mosaic', 'Nereid'
];
const previewAssistants = ['Codex', 'Claude', 'Gemini', null];
const previewProfiles = previewFamilies.map((name, index) => ({
  name,
  login: name.toLowerCase(),
  avatarIndex: index,
  avatarUrl: null
}));
let previewSeed = 0x51a7c0de;
function previewRandom() {
  previewSeed ^= previewSeed << 13;
  previewSeed ^= previewSeed >>> 17;
  previewSeed ^= previewSeed << 5;
  return (previewSeed >>> 0) / 4294967296;
}
const previewScores = Array.from({length: 50}, (_, index) => {
  const progress = index / 49;
  const signature = Math.max(512, Math.round(
    6100 * Math.exp(-1.45 * progress) * (.79 + .46 * previewRandom()) / 8
  ) * 8);
  const cycles = Math.max(8000, Math.round(
    90000 * Math.exp(-1.75 * progress) * (.77 + .5 * previewRandom())
  ));
  return {
    id: String(index + 1).padStart(3, '0'),
    name: previewFamilies[index % previewFamilies.length] + ' ' +
      (1 + Math.floor(index / previewFamilies.length)),
    profile: previewProfiles[index % previewProfiles.length],
    assistant: previewAssistants[index % previewAssistants.length],
    date: new Date(Date.UTC(2026, 1, 1 + index * 3)),
    signature,
    cycles,
    score: signature * cycles,
    record: false,
    gain: null
  };
});
// Deliberate tradeoffs make the fictional Pareto preview legible.
const previewTradeoffs = new Map([
  [42, [960, 32000]], [43, [1120, 24000]], [44, [1248, 18000]],
  [46, [1600, 13000]], [47, [1920, 11000]], [48, [2400, 9500]],
  [49, [3000, 8000]]
]);
for (const [index, [signature, cycles]] of previewTradeoffs) {
  Object.assign(previewScores[index], {signature, cycles, score: signature * cycles});
}
const previewRecords = [];
let previewRecordScore = Infinity;
for (const entry of previewScores) {
  if (entry.score < previewRecordScore) {
    entry.record = true;
    entry.gain = Number.isFinite(previewRecordScore) ? previewRecordScore - entry.score : null;
    previewRecords.push(entry);
    previewRecordScore = entry.score;
  }
}
const previewPareto = previewScores.filter(entry => !previewScores.some(other =>
  other !== entry && other.signature <= entry.signature && other.cycles <= entry.cycles &&
  (other.signature < entry.signature || other.cycles < entry.cycles)
)).sort((a, b) => a.signature - b.signature);
for (const entry of previewPareto) entry.pareto = true;
const previewFormat = value => value.toLocaleString('en-US');
const previewDate = date => date.toLocaleDateString('en-US', {
  month: 'short', day: 'numeric', year: 'numeric', timeZone: 'UTC'
});
const previewSubmissionUrl = entry => '/site/submission.html?id=' + entry.id;
const previewSolverUrl = profile => '/site/solver.html?user=' + encodeURIComponent(profile.login);
function previewAvatar(profile, className = 'lb-avatar') {
  if (profile.avatarUrl) {
    const img = document.createElement('img');
    img.className = className;
    img.src = profile.avatarUrl;
    img.alt = '';
    return img;
  }
  const avatar = document.createElement('span');
  avatar.className = className;
  avatar.setAttribute('aria-hidden', 'true');
  avatar.style.backgroundImage = "url('/site/assets/preview-profiles.png')";
  avatar.style.backgroundPosition =
    (profile.avatarIndex % 4) * 100 / 3 + '% ' +
    Math.floor(profile.avatarIndex / 4) * 100 / 3 + '%';
  return avatar;
}
window.previewScores = previewScores;
