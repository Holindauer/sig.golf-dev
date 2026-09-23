'use strict';

// Phony preview records. Remove this file and its script tag before launch.
const previewFamilies = [
  'Aster', 'Boreas', 'Cedar', 'Dorian', 'Echo', 'Fjord', 'Grove',
  'Helios', 'Iris', 'Juniper', 'Kite', 'Laurel', 'Mosaic', 'Nereid'
];
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
    name: previewFamilies[index % previewFamilies.length] + ' ' +
      (1 + Math.floor(index / previewFamilies.length)),
    date: new Date(Date.UTC(2026, 1, 1 + index * 3)),
    signature,
    cycles,
    score: signature * cycles
  };
});
const previewFormat = value => value.toLocaleString('en-US');
const previewRecords = [];
let previewRecordScore = Infinity;
for (const entry of previewScores) {
  if (entry.score < previewRecordScore) {
    previewRecords.push(entry);
    previewRecordScore = entry.score;
  }
}
document.querySelector('#best-score').textContent = previewFormat(previewRecordScore);

const previewLeaders = document.querySelector('#leaders');
previewLeaders.replaceChildren();
const recentRecords = previewRecords.slice(-10).reverse();
for (const [index, entry] of recentRecords.entries()) {
  const row = document.createElement('tr');
  row.className = 'lb-row' + (index === 0 ? ' current' : '');
  const solver = document.createElement('td');
  solver.className = 'lb-solver';
  for (const [className, value] of [
    ['lb-rank', String(index + 1).padStart(2, '0')],
    ['lb-avatar', entry.name[0]],
    ['lb-login', entry.name]
  ]) {
    const span = document.createElement('span');
    span.className = className;
    span.textContent = value;
    solver.appendChild(span);
  }
  row.appendChild(solver);
  const previous = previewRecords[previewRecords.indexOf(entry) - 1];
  const gain = previous ? '−' + previewFormat(previous.score - entry.score) : 'first record';
  for (const [text, className] of [
    [previewFormat(entry.score), 'number lb-score'],
    [previewFormat(entry.signature) + ' B', 'number'],
    [previewFormat(entry.cycles), 'number'],
    [gain, 'number lb-gain'],
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
  const values = previewScores.map(entry => Math.log(entry.score));
  const low = Math.min(...values);
  const high = Math.max(...values);
  const pad = (high - low) * .08;
  const minLog = low - pad;
  const maxLog = high + pad;
  const yFor = score => top + (maxLog - Math.log(score)) / (maxLog - minLog) * (bottom - top);
  const xFor = index => left + index / (previewScores.length - 1) * (dataRight - left);

  chartNode(chart, 'text', {
    x: left, y: 15, fill: '#737b80', 'font-size': '12',
    'font-family': 'system-ui, sans-serif'
  }, 'Score (log scale)');

  for (let tick = 0; tick <= 4; tick++) {
    const y = top + tick / 4 * (bottom - top);
    chartNode(chart, 'line', {
      x1: left, y1: y, x2: dataRight, y2: y,
      stroke: '#e3e5e5', 'stroke-width': '1'
    });
    const value = Math.exp(maxLog - tick / 4 * (maxLog - minLog));
    chartNode(chart, 'text', {
      x: left - 9, y: y + 4, 'text-anchor': 'end',
      fill: '#737b80', 'font-size': '11',
      'font-family': 'system-ui, sans-serif'
    }, compactScore(value));
  }
  chartNode(chart, 'line', {
    x1: left, y1: top, x2: left, y2: bottom,
    stroke: '#e3e5e5', 'stroke-width': '1'
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
    d: frontier + ' H' + dataRight, fill: 'none', stroke: '#286ec4',
    'stroke-width': '2.5', 'stroke-linejoin': 'round'
  });

  let runningBest = Infinity;
  previewScores.forEach((entry, index) => {
    const isRecord = entry.score < runningBest;
    runningBest = Math.min(runningBest, entry.score);
    const dot = chartNode(chart, 'circle', {
      cx: xFor(index), cy: yFor(entry.score),
      r: isRecord ? 4.5 : 2.5,
      fill: isRecord ? '#286ec4' : '#8caed1',
      stroke: isRecord ? '#fff' : 'none',
      'stroke-width': isRecord ? '1.8' : '0',
      opacity: isRecord ? '1' : '.75', tabindex: '0'
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
      fill: 'none', stroke: '#286ec4', 'stroke-width': '1.4'
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
renderPreviewChart();
addEventListener('resize', () => requestAnimationFrame(renderPreviewChart));
window.previewScores = previewScores;
