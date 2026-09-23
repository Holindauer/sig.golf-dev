'use strict';

const chartGrid = '#c1d1e4';
const chartAxis = '#8ca7c5';
const chartLine = '#1c5fa9';

// Phony preview records. Replace with verified submission data before launch.
document.querySelector('#best-score').textContent = previewFormat(previewRecordScore);

const previewLeaders = document.querySelector('#leaders');
previewLeaders.replaceChildren();
const sortedEntries = [...previewScores].sort((a, b) => a.score - b.score || a.date - b.date);
for (const [index, entry] of sortedEntries.entries()) {
  const row = document.createElement('tr');
  row.className = 'lb-row' + (index === 0 ? ' current' : '');
  row.addEventListener('click', event => {
    if (!event.target.closest('a')) location.href = previewSubmissionUrl(entry);
  });
  const solver = document.createElement('td');
  solver.className = 'lb-solver';
  const rank = document.createElement('span');
  rank.className = 'lb-rank';
  rank.textContent = String(index + 1).padStart(2, '0');
  solver.append(rank, previewAvatar(entry.profile));
  const solverLink = document.createElement('a');
  solverLink.className = 'lb-login';
  solverLink.href = previewSolverUrl(entry.profile);
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
  scoreLink.href = previewSubmissionUrl(entry);
  scoreLink.textContent = previewFormat(entry.score);
  score.appendChild(scoreLink);
  row.appendChild(score);
  for (const [text, className] of [
    [previewFormat(entry.signature) + ' B', 'number'],
    [previewFormat(entry.cycles), 'number'],
    [entry.date.toLocaleDateString('en-US', {month: 'short', day: 'numeric', timeZone: 'UTC'}), 'number lb-date']
  ]) {
    const cell = document.createElement('td');
    cell.className = className;
    cell.textContent = text;
    row.appendChild(cell);
  }
  previewLeaders.appendChild(row);
}

const previewChartNS = 'http://www.w3.org/2000/svg';
function chartNode(parent, tag, attributes, content) {
  const node = document.createElementNS(previewChartNS, tag);
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, value);
  if (content !== undefined) node.textContent = content;
  parent.appendChild(node);
  return node;
}
function compactScore(value) {
  if (value === 0) return '0';
  if (value >= 1000000000) return (value / 1000000000).toFixed(1) + 'B';
  if (value >= 1000000) return Math.round(value / 1000000) + 'M';
  return Math.round(value / 1000) + 'k';
}
function renderPreviewChart() {
  const chart = document.querySelector('#score-chart');
  const width = Math.round(chart.clientWidth);
  const height = Math.round(chart.clientHeight);
  if (!width || !height) return;
  chart.setAttribute('viewBox', '0 0 ' + width + ' ' + height);
  chart.replaceChildren();

  const desktop = width > 760;
  const left = desktop ? 58 : 46;
  const top = 36;
  const bottom = height - 36;
  const dataRight = width - (desktop ? 205 : 14);
  const maxScore = Math.max(...previewScores.map(entry => entry.score));
  const axisMax = Math.ceil(maxScore / 250000000) * 250000000;
  const yFor = score => top + (axisMax - score) / axisMax * (bottom - top);
  const xFor = index => left + index / (previewScores.length - 1) * (dataRight - left);

  chartNode(chart, 'text', {
    x: left, y: 15, fill: '#737b80', 'font-size': '12',
    'font-family': 'system-ui, sans-serif'
  }, 'Score');

  for (let tick = 0; tick <= 4; tick++) {
    const y = top + tick / 4 * (bottom - top);
    chartNode(chart, 'line', {
      x1: left, y1: y, x2: dataRight, y2: y,
      stroke: chartGrid, 'stroke-width': '1'
    });
    const value = axisMax * (1 - tick / 4);
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

  let best = Infinity;
  let frontier = '';
  previewScores.forEach((entry, index) => {
    const x = xFor(index);
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
    d: frontier + ' H' + dataRight + ' V' + bottom + ' H' + left + ' Z',
    fill: 'url(#record-fill)'
  });
  chartNode(chart, 'path', {
    d: frontier + ' H' + dataRight, fill: 'none', stroke: chartLine,
    'stroke-width': '2.5', 'stroke-linejoin': 'round'
  });

  let runningBest = Infinity;
  previewScores.forEach((entry, index) => {
    const isRecord = entry.score < runningBest;
    runningBest = Math.min(runningBest, entry.score);
    const point = chartNode(chart, 'a', {
      href: previewSubmissionUrl(entry), tabindex: '0',
      'aria-label': entry.name + ', score ' + previewFormat(entry.score) + '. View submission.'
    });
    chartNode(point, 'circle', {
      class: 'hit-area', cx: xFor(index), cy: yFor(entry.score), r: 12
    });
    const dot = chartNode(point, 'circle', {
      cx: xFor(index), cy: yFor(entry.score),
      r: isRecord ? 4.5 : 3.2,
      fill: isRecord ? '#286ec4' : '#5f8fbe',
      stroke: isRecord ? '#fff' : 'none',
      'stroke-width': isRecord ? '1.8' : '0',
      opacity: isRecord ? '1' : '.9'
    });
    chartNode(dot, 'title', {},
      entry.name + ' · ' + entry.date.toISOString().slice(0, 10) +
      ' · ' + previewFormat(entry.signature) + ' B × ' +
      previewFormat(entry.cycles) + ' cycles = ' + previewFormat(entry.score));
  });

  for (let tick = 0; tick < (desktop ? 5 : 3); tick++) {
    const total = desktop ? 4 : 2;
    const index = Math.round(tick / total * (previewScores.length - 1));
    const x = xFor(index);
    const label = previewScores[index].date.toLocaleDateString('en-US', {
      month: 'short', day: 'numeric', timeZone: 'UTC'
    });
    chartNode(chart, 'text', {
      x, y: height - 9, 'text-anchor': tick === 0 ? 'start' : tick === total ? 'end' : 'middle',
      fill: '#737b80', 'font-size': '11',
      'font-family': 'system-ui, sans-serif'
    }, label);
  }
  if (desktop) {
    const lastY = yFor(previewRecordScore);
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
    }, previewFormat(previewRecordScore));
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
  const maxSignature = Math.ceil(Math.max(...previewScores.map(x => x.signature)) / 1000) * 1000;
  const maxCycles = Math.ceil(Math.max(...previewScores.map(x => x.cycles)) / 20000) * 20000;
  const xFor = signature => left + signature / maxSignature * (right - left);
  const yFor = cycles => top + (maxCycles - cycles) / maxCycles * (bottom - top);

  chartNode(chart, 'text', {
    x: left, y: 15, fill: '#737b80', 'font-size': '12',
    'font-family': 'system-ui, sans-serif'
  }, width < 340 ? 'Cycles' : 'Verification cycles');
  chartNode(chart, 'text', {
    x: (left + right) / 2, y: height - 5, 'text-anchor': 'middle',
    fill: '#737b80', 'font-size': '12', 'font-family': 'system-ui, sans-serif'
  }, 'Signature size (bytes) →');
  for (let tick = 0; tick <= 4; tick++) {
    const y = top + tick / 4 * (bottom - top);
    const x = left + tick / 4 * (right - left);
    chartNode(chart, 'line', {
      x1: left, y1: y, x2: right, y2: y, stroke: chartGrid, 'stroke-width': '1'
    });
    chartNode(chart, 'text', {
      x: left - 9, y: y + 4, 'text-anchor': 'end', fill: '#737b80',
      'font-size': '11', 'font-family': 'system-ui, sans-serif'
    }, compactScore(maxCycles * (1 - tick / 4)));
    chartNode(chart, 'text', {
      x, y: bottom + 18, 'text-anchor': tick === 0 ? 'start' : tick === 4 ? 'end' : 'middle',
      fill: '#737b80', 'font-size': '11', 'font-family': 'system-ui, sans-serif'
    }, previewFormat(maxSignature * tick / 4));
  }
  chartNode(chart, 'line', {
    x1: left, y1: top, x2: left, y2: bottom, stroke: chartAxis, 'stroke-width': '1'
  });

  const frontier = previewPareto.map((entry, index) =>
    (index ? ' L' : 'M') + xFor(entry.signature).toFixed(1) + ' ' +
    yFor(entry.cycles).toFixed(1)).join('');
  chartNode(chart, 'path', {
    d: frontier, fill: 'none', stroke: chartLine,
    'stroke-width': '2.5', 'stroke-linejoin': 'round'
  });
  for (const entry of [...previewScores.filter(x => !x.pareto), ...previewPareto]) {
    const point = chartNode(chart, 'a', {
      href: previewSubmissionUrl(entry), tabindex: '0',
      'aria-label': entry.name + ', ' + previewFormat(entry.signature) +
        ' signature bytes and ' + previewFormat(entry.cycles) +
        ' verification cycles. View submission.'
    });
    chartNode(point, 'circle', {
      class: 'hit-area', cx: xFor(entry.signature), cy: yFor(entry.cycles), r: 12
    });
    const dot = chartNode(point, 'circle', {
      cx: xFor(entry.signature), cy: yFor(entry.cycles),
      r: entry.pareto ? 5 : 3.6, fill: entry.pareto ? '#286ec4' : '#5f8fbe',
      stroke: entry.pareto ? '#fff' : 'none',
      'stroke-width': entry.pareto ? '1.8' : '0',
      opacity: entry.pareto ? '1' : '.88'
    });
    chartNode(dot, 'title', {}, entry.name + ' · ' +
      previewFormat(entry.signature) + ' B × ' + previewFormat(entry.cycles) +
      ' cycles = ' + previewFormat(entry.score) +
      (entry.pareto ? ' · Pareto frontier' : ''));
  }
}
renderPreviewChart();
renderParetoChart();
addEventListener('resize', () => requestAnimationFrame(() => {
  renderPreviewChart();
  renderParetoChart();
}));
