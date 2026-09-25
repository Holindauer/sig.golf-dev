'use strict';

async function loadRecords() {
  const [response, stateResponse] = await Promise.all([
    fetch('/records.json', {cache: 'no-store'}),
    fetch('/state.json', {cache: 'no-store'})
  ]);
  if (!response.ok || !stateResponse.ok) throw new Error('Cannot load published records');
  const [registry, state] = await Promise.all([response.json(), stateResponse.json()]);
  if (registry.version !== 1 || !Array.isArray(registry.submissions)) throw new Error('Invalid record registry');
  if (!/^[0-9a-f]{40}$/.test(state.contract_commit || '')) return [];
  return registry.submissions.filter(item =>
    item.contract_commit === state.contract_commit && typeof item.id === 'string' && typeof item.author === 'string' &&
    typeof item.score === 'string' && /^\d+$/.test(item.score) &&
    Number.isSafeInteger(item.S) && Number.isSafeInteger(item.C) &&
    Number.isFinite(Date.parse(item.verified_at))
  ).map(item => ({
    ...item,
    name: item.title || `PR #${item.pr}`,
    profile: {login: item.author, avatarUrl: item.avatar_url},
    assistant: item.assisted_by,
    date: new Date(item.verified_at),
    signature: item.S,
    cycles: item.C,
    score: Number(item.score),
    scoreExact: BigInt(item.score)
  })).sort((a, b) => a.date - b.date);
}

const format = value => value.toLocaleString('en-US');
const submissionUrl = item => '/submission.html?id=' + encodeURIComponent(item.id);
const solverUrl = profile => '/solver.html?user=' + encodeURIComponent(profile.login);
function avatar(profile, className = 'lb-avatar') {
  const img = document.createElement('img');
  img.className = className;
  img.src = profile.avatarUrl || `https://github.com/${encodeURIComponent(profile.login)}.png?size=64`;
  img.alt = '';
  img.loading = 'lazy';
  return img;
}

async function renderRecords() {
  const scores = await loadRecords();
  if (!scores.length) return;
  const bestExact = scores.reduce((best, item) => item.scoreExact < best ? item.scoreExact : best,
    scores[0].scoreExact);
  const bestScore = Number(bestExact);
  const pareto = scores.filter(entry => !scores.some(other => other !== entry &&
    other.signature <= entry.signature && other.cycles <= entry.cycles &&
    (other.signature < entry.signature || other.cycles < entry.cycles)
  )).sort((a, b) => a.signature - b.signature || a.cycles - b.cycles);
  for (const entry of pareto) entry.pareto = true;
  for (const [section, id] of [['.progress', 'score-chart'], ['.pareto', 'pareto-chart']]) {
    const placeholder = document.querySelector(section + ' .score-plot');
    const svg = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    svg.setAttribute('id', id);
    svg.setAttribute('class', 'score-plot');
    svg.setAttribute('width', '100%');
    svg.setAttribute('role', 'img');
    svg.setAttribute('aria-label', section === '.progress' ? 'Verified scores over time' : 'Signature size and verification cycle Pareto frontier');
    placeholder.replaceWith(svg);
  }
const chartGrid = '#c1d1e4';
const chartAxis = '#8ca7c5';
const chartLine = '#1c5fa9';

document.querySelector('#best-score').textContent = format(bestExact);

const leaders = document.querySelector('#leaders');
leaders.replaceChildren();
const sortedEntries = [...scores].sort((a, b) => a.scoreExact < b.scoreExact ? -1 : a.scoreExact > b.scoreExact ? 1 : a.date - b.date);
for (const [index, entry] of sortedEntries.entries()) {
  const row = document.createElement('tr');
  row.className = 'lb-row' + (index === 0 ? ' current' : '');
  row.addEventListener('click', event => {
    if (!event.target.closest('a')) location.href = submissionUrl(entry);
  });
  const solver = document.createElement('td');
  solver.className = 'lb-solver';
  const rank = document.createElement('span');
  rank.className = 'lb-rank';
  rank.textContent = String(index + 1).padStart(2, '0');
  solver.append(rank, avatar(entry.profile));
  const solverLink = document.createElement('a');
  solverLink.className = 'lb-login';
  solverLink.href = solverUrl(entry.profile);
  solverLink.textContent = entry.profile.login;
  solver.appendChild(solverLink);
  if (entry.assistant) {
    const badge = document.createElement('span');
    badge.className = 'lb-model';
    badge.textContent = entry.assistant;
    badge.title = 'Assisted by ' + entry.assistant;
    solver.appendChild(badge);
  }
  row.appendChild(solver);
  const score = document.createElement('td');
  score.className = 'number lb-score';
  const scoreLink = document.createElement('a');
  scoreLink.href = submissionUrl(entry);
  scoreLink.textContent = format(entry.scoreExact);
  score.appendChild(scoreLink);
  row.appendChild(score);
  for (const [text, className] of [
    [format(entry.signature) + ' B', 'number'],
    [format(entry.cycles), 'number'],
    [entry.date.toLocaleDateString('en-US', {month: 'short', day: 'numeric', timeZone: 'UTC'}), 'number lb-date']
  ]) {
    const cell = document.createElement('td');
    cell.className = className;
    cell.textContent = text;
    row.appendChild(cell);
  }
  leaders.appendChild(row);
}

const chartNS = 'http://www.w3.org/2000/svg';
function chartNode(parent, tag, attributes, content) {
  const node = document.createElementNS(chartNS, tag);
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, value);
  if (content !== undefined) node.textContent = content;
  parent.appendChild(node);
  return node;
}
function compactScore(value) {
  const [unit, suffix] = [[1e9, 'B'], [1e6, 'M'], [1e3, 'k']].find(([unit]) => value >= unit) || [1, ''];
  const scaled = value / unit;
  const digits = [0, 1, 2].find(d => Math.abs(Math.round(scaled * 10 ** d) - scaled * 10 ** d) < 1e-6) ?? 3;
  return scaled.toFixed(digits) + suffix;
}
// Logarithmic axis fitted to the data. Ticks are powers of ten, then 1-2-5 steps, then linear steps for narrow ranges.
function logScale(values, intervals = 4) {
  const low = Math.log10(Math.max(1, Math.min(...values)));
  const high = Math.log10(Math.max(1, Math.max(...values)));
  const padding = Math.max((high - low) * .08, .02);
  const min = 10 ** (low - padding);
  const max = 10 ** (high + padding);
  const fraction = value => (Math.log10(Math.max(1, value)) - low + padding) / (high - low + 2 * padding);
  return {fraction, ticks: logTicks(min, max, intervals)};
}
function logTicks(min, max, intervals) {
  const stride = Math.max(1, Math.round(Math.log10(max / min) / intervals));
  for (const mantissas of [[1], [1, 2, 5], [1, 1.5, 2, 3, 5, 7]]) {
    const ticks = [];
    for (let exponent = Math.floor(Math.log10(min)); exponent <= Math.ceil(Math.log10(max));
      exponent += mantissas.length === 1 ? stride : 1) {
      for (const mantissa of mantissas) {
        const value = mantissa * 10 ** exponent;
        if (value >= min && value <= max) ticks.push(value);
      }
    }
    if (ticks.length >= 3) return ticks;
  }
  let ticks = [];
  for (let exponent = Math.floor(Math.log10(max - min)); ticks.length < 3; exponent--) {
    for (const mantissa of [5, 2, 1]) {
      const step = mantissa * 10 ** exponent;
      ticks = [];
      for (let index = Math.ceil(min / step); index * step <= max; index++) ticks.push(index * step);
      if (ticks.length >= 3) break;
    }
  }
  return ticks;
}
function renderScoreChart() {
  const chart = document.querySelector('#score-chart');
  const width = Math.round(chart.clientWidth);
  const height = Math.round(chart.clientHeight);
  if (!width || !height) return;
  chart.setAttribute('viewBox', '0 0 ' + width + ' ' + height);
  chart.replaceChildren();

  const desktop = width > 760;
  const left = desktop ? 58 : 46;
  const top = 36;
  const bottom = height - 58;
  const dataRight = width - (desktop ? 165 : 14);
  const scoreScale = logScale(scores.map(entry => entry.score), 5);
  const yFor = score => bottom - scoreScale.fraction(score) * (bottom - top);
  const firstTime = scores[0].date.getTime();
  const lastTime = scores[scores.length - 1].date.getTime();
  const timeSpan = lastTime - firstTime;
  const xFor = date => left + (timeSpan ? (date.getTime() - firstTime) / timeSpan : .5) * (dataRight - left);

  chartNode(chart, 'text', {
    x: left, y: 15, fill: '#737b80', 'font-size': '12',
    'font-family': 'system-ui, sans-serif'
  }, 'Score (log scale)');

  const firstDay = scores[0].date.toISOString().slice(0, 10);
  const lastDay = scores[scores.length - 1].date.toISOString().slice(0, 10);
  const dayLabel = date => date.toLocaleDateString('en-US', {month: 'short', day: 'numeric', timeZone: 'UTC'});
  chartNode(chart, 'text', {
    x: dataRight, y: height - 9, 'text-anchor': 'end', fill: '#737b80',
    'font-size': '11', 'font-family': 'system-ui, sans-serif'
  }, (firstDay === lastDay ? dayLabel(scores[0].date) :
    dayLabel(scores[0].date) + '–' + dayLabel(scores[scores.length - 1].date)) + ' · UTC');
  for (const value of scoreScale.ticks) {
    const y = yFor(value);
    chartNode(chart, 'line', {
      x1: left, y1: y, x2: dataRight, y2: y,
      stroke: chartGrid, 'stroke-width': '1'
    });
    chartNode(chart, 'text', {
      x: left - 9, y: y + 4, 'text-anchor': 'end',
      fill: '#737b80', 'font-size': '11',
      'font-family': 'system-ui, sans-serif'
    }, compactScore(value));
  }
  chartNode(chart, 'line', {
    x1: left, y1: top, x2: left, y2: bottom,
    stroke: chartAxis, 'stroke-width': '1'
  });
  chartNode(chart, 'line', {
    x1: left, y1: bottom, x2: dataRight, y2: bottom,
    stroke: chartAxis, 'stroke-width': '1'
  });

  let best = Infinity;
  let frontier = '';
  scores.forEach((entry, index) => {
    const x = xFor(entry.date);
    if (index === 0) {
      best = entry.score;
      frontier = 'M' + x.toFixed(1) + ' ' + yFor(best).toFixed(1);
    } else {
      frontier += ' H' + x.toFixed(1);
      if (entry.score < best) {
        best = entry.score;
        frontier += ' V' + yFor(best).toFixed(1);
      }
    }
  });
  const gradient = chartNode(chartNode(chart, 'defs', {}), 'linearGradient', {
    id: 'record-fill', x1: '0', y1: '0', x2: '0', y2: '1'
  });
  chartNode(gradient, 'stop', {offset: '0%', 'stop-color': '#cde3f8', 'stop-opacity': '.65'});
  chartNode(gradient, 'stop', {offset: '100%', 'stop-color': '#fff', 'stop-opacity': '0'});
  chartNode(chart, 'path', {
    d: frontier + ' H' + dataRight + ' V' + bottom + ' H' + xFor(scores[0].date) + ' Z',
    fill: 'url(#record-fill)'
  });
  chartNode(chart, 'path', {
    d: frontier + ' H' + dataRight, fill: 'none', stroke: chartLine,
    'stroke-width': '2.5', 'stroke-linejoin': 'round'
  });

  let runningBest = Infinity;
  scores.forEach((entry, index) => {
    const isRecord = entry.score < runningBest;
    runningBest = Math.min(runningBest, entry.score);
    const point = chartNode(chart, 'a', {
      href: submissionUrl(entry), tabindex: '0',
      'aria-label': entry.name + ', score ' + format(entry.scoreExact) + '. View submission.'
    });
    chartNode(point, 'circle', {
      class: 'hit-area', cx: xFor(entry.date), cy: yFor(entry.score), r: 12,
      fill: 'transparent', stroke: 'none', 'pointer-events': 'all'
    });
    const dot = chartNode(point, 'circle', {
      cx: xFor(entry.date), cy: yFor(entry.score),
      r: isRecord ? 4.5 : 3.2,
      fill: isRecord ? '#286ec4' : '#5f8fbe',
      stroke: isRecord ? '#fff' : 'none',
      'stroke-width': isRecord ? '1.8' : '0',
      opacity: isRecord ? '1' : '.9'
    });
    chartNode(dot, 'title', {},
      entry.name + ' · ' + entry.date.toISOString().slice(0, 10) +
      ' · ' + format(entry.signature) + ' B × ' +
      format(entry.cycles) + ' cycles = ' + format(entry.scoreExact));
  });

  const ticks = timeSpan ? (desktop ? 4 : 2) : 0;
  for (let tick = 0; tick <= ticks; tick++) {
    const fraction = ticks ? tick / ticks : .5;
    const date = new Date(firstTime + fraction * timeSpan);
    const x = left + fraction * (dataRight - left);
    const label = firstDay === lastDay ? date.toLocaleTimeString('en-GB', {
      hour: '2-digit', minute: '2-digit', timeZone: 'UTC'
    }) : dayLabel(date);
    chartNode(chart, 'text', {
      x, y: bottom + 24, 'text-anchor': tick === 0 && ticks ? 'start' : tick === ticks && ticks ? 'end' : 'middle',
      fill: '#737b80', 'font-size': '11',
      'font-family': 'system-ui, sans-serif'
    }, label);
  }
  if (desktop) {
    const lastY = yFor(bestScore);
    chartNode(chart, 'path', {
      d: 'M' + dataRight + ' ' + lastY + ' h12',
      fill: 'none', stroke: chartLine, 'stroke-width': '1.4'
    });
    chartNode(chart, 'text', {
      x: dataRight + 18, y: lastY - 7, fill: '#737b80',
      'font-size': '11', 'font-family': 'system-ui, sans-serif'
    }, 'Best score');
    chartNode(chart, 'text', {
      x: dataRight + 18, y: lastY + 14, fill: '#111518',
      'font-size': '15', 'font-weight': '700',
      'font-family': 'system-ui, sans-serif'
    }, format(bestExact));
  }
}
function renderParetoChart() {
  const chart = document.querySelector('#pareto-chart');
  const width = Math.round(chart.clientWidth);
  const height = Math.round(chart.clientHeight);
  if (!width || !height) return;
  chart.setAttribute('viewBox', '0 0 ' + width + ' ' + height);
  chart.replaceChildren();

  const left = width > 760 ? 64 : 48;
  const right = width - 22;
  const top = 34;
  const bottom = height - 58;
  const signatureScale = logScale(scores.map(x => x.signature));
  const cycleScale = logScale(scores.map(x => x.cycles));
  const xFor = signature => left + signatureScale.fraction(signature) * (right - left);
  const yFor = cycles => bottom - cycleScale.fraction(cycles) * (bottom - top);

  chartNode(chart, 'text', {
    x: left, y: 15, fill: '#737b80', 'font-size': '12',
    'font-family': 'system-ui, sans-serif'
  }, width < 340 ? 'Cycles (log)' : 'Verification cycles (log scale)');
  chartNode(chart, 'text', {
    x: (left + right) / 2, y: height - 5, 'text-anchor': 'middle',
    fill: '#737b80', 'font-size': '12', 'font-family': 'system-ui, sans-serif'
  }, 'Signature size (bytes, log scale) →');
  if (pareto.length === 1) {
    const entry = pareto[0];
    chartNode(chart, 'rect', {
      x: xFor(entry.signature), y: top, width: right - xFor(entry.signature),
      height: yFor(entry.cycles) - top, fill: chartLine, opacity: '.045'
    });
  }
  for (const value of cycleScale.ticks) {
    const y = yFor(value);
    chartNode(chart, 'line', {
      x1: left, y1: y, x2: right, y2: y, stroke: chartGrid, 'stroke-width': '1'
    });
    chartNode(chart, 'text', {
      x: left - 9, y: y + 4, 'text-anchor': 'end', fill: '#737b80',
      'font-size': '11', 'font-family': 'system-ui, sans-serif'
    }, compactScore(value));
  }
  for (const value of signatureScale.ticks) {
    const x = xFor(value);
    chartNode(chart, 'line', {
      x1: x, y1: top, x2: x, y2: bottom, stroke: chartGrid, 'stroke-width': '1'
    });
    chartNode(chart, 'text', {
      x, y: bottom + 18,
      'text-anchor': x - left < 24 ? 'start' : right - x < 24 ? 'end' : 'middle',
      fill: '#737b80', 'font-size': '11', 'font-family': 'system-ui, sans-serif'
    }, compactScore(value));
  }
  chartNode(chart, 'line', {
    x1: left, y1: top, x2: left, y2: bottom, stroke: chartAxis, 'stroke-width': '1'
  });
  chartNode(chart, 'line', {
    x1: left, y1: bottom, x2: right, y2: bottom, stroke: chartAxis, 'stroke-width': '1'
  });

  const frontier = pareto.map((entry, index) =>
    (index ? ' L' : 'M') + xFor(entry.signature).toFixed(1) + ' ' +
    yFor(entry.cycles).toFixed(1)).join('');
  if (pareto.length > 1) chartNode(chart, 'path', {
    d: frontier, fill: 'none', stroke: chartLine,
    'stroke-width': '2.5', 'stroke-linejoin': 'round'
  });
  for (const entry of [...scores.filter(x => !x.pareto), ...pareto]) {
    const point = chartNode(chart, 'a', {
      href: submissionUrl(entry), tabindex: '0',
      'aria-label': entry.name + ', ' + format(entry.signature) +
        ' signature bytes and ' + format(entry.cycles) +
        ' verification cycles. View submission.'
    });
    chartNode(point, 'circle', {
      class: 'hit-area', cx: xFor(entry.signature), cy: yFor(entry.cycles), r: 12,
      fill: 'transparent', stroke: 'none', 'pointer-events': 'all'
    });
    if (entry.pareto) chartNode(point, 'circle', {
      cx: xFor(entry.signature), cy: yFor(entry.cycles), r: 11,
      fill: chartLine, opacity: '.16'
    });
    const dot = chartNode(point, 'circle', {
      cx: xFor(entry.signature), cy: yFor(entry.cycles),
      r: entry.pareto ? 6 : 4, fill: entry.pareto ? '#286ec4' : '#638bb8',
      stroke: '#fff', 'stroke-width': entry.pareto ? '2' : '1',
      opacity: entry.pareto ? '1' : '.7'
    });
    chartNode(dot, 'title', {}, entry.name + ' · ' +
      format(entry.signature) + ' B × ' + format(entry.cycles) +
      ' cycles = ' + format(entry.scoreExact) +
      (entry.pareto ? ' · Pareto frontier' : ''));
  }
  if (pareto.length === 1) {
    const entry = pareto[0];
    const pointX = xFor(entry.signature);
    const pointY = yFor(entry.cycles);
    const label = chartNode(chart, 'a', {
      href: submissionUrl(entry), tabindex: '0',
      'aria-label': 'Only Pareto frontier point: PR #' + entry.pr
    });
    chartNode(label, 'text', {
      x: pointX + (pointX > right - 160 ? -14 : 14), y: pointY - 12,
      'text-anchor': pointX > right - 160 ? 'end' : 'start',
      fill: chartLine, 'font-size': '12', 'font-weight': '700',
      'font-family': 'system-ui, sans-serif'
    }, 'Frontier · PR #' + entry.pr);
  }
}
renderScoreChart();
renderParetoChart();
addEventListener('resize', () => requestAnimationFrame(() => {
  renderScoreChart();
  renderParetoChart();
}));

}
renderRecords().catch(error => {
  console.error('Unable to display verified records:', error);
  for (const node of document.querySelectorAll('.empty-plot-message, .empty-row'))
    node.textContent = 'Verified records are temporarily unavailable.';
});
