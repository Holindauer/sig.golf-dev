'use strict';

const NS = 'http://www.w3.org/2000/svg';
const $ = selector => document.querySelector(selector);
const handInImage = {x: 548, y: 148};
const BOLT_HOLD_MS = 1000;
const BOLT_FADE_MS = 500;
const BOLT_ARRIVAL_MS = 380;
const FIRST_STRIKE_MIN_MS = 2000;
const FIRST_STRIKE_MAX_MS = 4000;
const STRIKE_INTERVAL_MIN_MS = 5000;
const STRIKE_INTERVAL_MAX_MS = 10000;
const mix = (a, b, t) => a + (b - a) * t;
const clamp = (value, lo = 0, hi = 1) => Math.max(lo, Math.min(hi, value));
const randomWord = () => {
  const bytes = new Uint32Array(1);
  crypto.getRandomValues(bytes);
  return bytes[0];
};
const unit = () => randomWord() / 4294967296;
const nextIntervalMs = () => STRIKE_INTERVAL_MIN_MS + unit() * (STRIKE_INTERVAL_MAX_MS - STRIKE_INTERVAL_MIN_MS);

let lastStrike = -Infinity;
let nextStrike = performance.now() + FIRST_STRIKE_MIN_MS + unit() * (FIRST_STRIKE_MAX_MS - FIRST_STRIKE_MIN_MS);
let paused = matchMedia('(prefers-reduced-motion: reduce)').matches;
let layout = [];
let pageRoute = [];
let pageHand = null;
let lastLeaves = null;
let boltLength = 0;
let treeGroups = [];

function element(tag, attributes, parent) {
  const node = document.createElementNS(NS, tag);
  for (const [key, value] of Object.entries(attributes)) node.setAttribute(key, value);
  parent.appendChild(node);
  return node;
}

function handOnPage() {
  const image = $('#zeus-full');
  if (!image.complete || !image.naturalWidth) return null;
  const rect = image.getBoundingClientRect();
  return {
    x: rect.left + scrollX + rect.width * handInImage.x / image.naturalWidth,
    y: rect.top + scrollY + rect.height * handInImage.y / image.naturalHeight
  };
}

function pathData(points) {
  return 'M' + points.map(point => point.x.toFixed(2) + ' ' + point.y.toFixed(2)).join(' L');
}

function jaggedEdge(a, b, segments = 3, jitter = 10) {
  const dx = b.x - a.x;
  const dy = b.y - a.y;
  const length = Math.hypot(dx, dy) || 1;
  const normal = {x: -dy / length, y: dx / length};
  const points = [a];
  for (let i = 1; i < segments; i++) {
    const t = i / segments;
    const offset = (unit() - .5) * Math.min(jitter, length * .27);
    points.push({
      x: mix(a.x, b.x, t) + normal.x * offset,
      y: mix(a.y, b.y, t) + normal.y * offset
    });
  }
  points.push(b);
  return points;
}

function selectedIds(leaf) {
  const ids = [];
  while (leaf > 1) {
    ids.unshift(leaf);
    leaf >>= 1;
  }
  return ids;
}

function treeShape(root, target, leaf, width, baseSpread) {
  // Swapping left and right children changes the drawing without changing the selected XMSS path.
  const options = Array.from({length: 16}, (_, visualLeaf) => {
    const selectedX = (visualLeaf + .5) / 8 - 1;
    const leftRoom = (target.x - 12) / (.9375 + selectedX);
    const rightRoom = (width - 12 - target.x) / (.9375 - selectedX);
    return {visualLeaf, spread: Math.min(baseSpread, leftRoom, rightRoom)};
  });
  const roomy = options.filter(option => option.spread >= baseSpread * .72);
  const choices = roomy.length ? roomy : options.sort((a, b) => b.spread - a.spread).slice(0, 4);
  const choice = choices[randomWord() % choices.length];
  const spread = Math.max(20, choice.spread);
  const mask = (leaf - 16) ^ choice.visualLeaf;
  const selectedX = (choice.visualLeaf + .5) / 8 - 1;
  const points = Array(32);

  for (let id = 1; id < 32; id++) {
    const depth = Math.floor(Math.log2(id));
    const index = id - (1 << depth);
    const visual = index ^ (mask >> (4 - depth));
    const t = depth / 4;
    const x = (visual + .5) / (1 << depth) * 2 - 1;
    points[id] = {
      x: mix(root.x, target.x, t) + spread * (x - selectedX * t) + (unit() - .5) * 22,
      y: mix(root.y, target.y, t) + (unit() - .5) * Math.min(17, (target.y - root.y) * .18)
    };
  }
  points[1] = root;
  points[leaf] = target;
  return points;
}

function newStrike() {
  const hand = handOnPage();
  if (!hand) return false;
  const overlay = $('#page-bolt');
  const width = Math.max(document.documentElement.clientWidth, document.documentElement.scrollWidth);
  const height = document.documentElement.scrollHeight;
  overlay.style.width = width + 'px';
  overlay.style.height = height + 'px';
  overlay.setAttribute('viewBox', '0 0 ' + width + ' ' + height);

  pageHand = hand;
  const topRange = clamp(width * .045, 18, 55);
  const top = {x: clamp(pageHand.x + (unit() - .5) * topRange * 2, 20, width - 20), y: -18};
  const skyGlow = $('#sky-glow');
  skyGlow.setAttribute('cx', mix(top.x, pageHand.x, .4));
  skyGlow.setAttribute('cy', pageHand.y * .3);
  skyGlow.setAttribute('rx', Math.min(680, width * .55));
  skyGlow.setAttribute('ry', clamp(pageHand.y * .9, 150, 340));
  const firstY = clamp(pageHand.y * .06, 24, 44);
  const gap = clamp(pageHand.y * .035, 18, 28);
  const span = (pageHand.y - firstY - 2 * gap) / 3;
  const inside = x => clamp(x, width * .16, width * .84);

  const firstRoot = inside(top.x);
  const firstEnd = inside(mix(firstRoot, pageHand.x, .32) + (unit() - .5) * width * .22);
  const secondRoot = inside(firstEnd + (unit() - .5) * width * .07);
  const secondEnd = inside(mix(secondRoot, pageHand.x, .53) + (unit() - .5) * width * .17);
  const thirdRoot = inside(secondEnd + (unit() - .5) * width * .07);
  const roots = [
    {x: firstRoot, y: firstY},
    {x: secondRoot, y: firstY + span + gap},
    {x: thirdRoot, y: firstY + 2 * (span + gap)}
  ];
  const targets = [
    {x: firstEnd, y: firstY + span},
    {x: secondEnd, y: firstY + 2 * span + gap},
    pageHand
  ];

  let leaves;
  do {
    leaves = Array.from({length: 3}, () => 16 + (randomWord() & 15));
  } while (lastLeaves && leaves.every((leaf, index) => leaf === lastLeaves[index]));
  lastLeaves = leaves;

  const trees = $('#trees');
  trees.replaceChildren();
  treeGroups = [];
  pageRoute = jaggedEdge(top, roots[0], 5, 18);
  layout = [];
  const baseSpread = clamp(width * .23, 85, 235);

  for (let treeIndex = 0; treeIndex < 3; treeIndex++) {
    const root = roots[treeIndex];
    const target = targets[treeIndex];
    const leaf = leaves[treeIndex];
    const points = treeShape(root, target, leaf, width, baseSpread);
    const group = element('g', {'stroke-linecap': 'round', 'stroke-linejoin': 'round', opacity: '0'}, trees);
    treeGroups.push(group);
    element('ellipse', {
      cx: mix(root.x, target.x, .5), cy: mix(root.y, target.y, .5),
      rx: Math.min(baseSpread * 1.18, width * .3), ry: Math.max(28, span * .75),
      fill: 'url(#treeflash)', stroke: 'none'
    }, group);
    const branches = element('g', {fill: 'none'}, group);
    const aura = element('g', {filter: 'url(#branch-blur)'}, branches);
    const body = element('g', {}, branches);
    const shine = element('g', {}, branches);
    const edges = [];
    for (let id = 2; id < 32; id++) {
      const edge = jaggedEdge(points[id >> 1], points[id], 4, 17);
      edges[id] = edge;
      const depth = Math.floor(Math.log2(id));
      const d = pathData(edge);
      const widthAtDepth = [0, 3.1, 2.5, 1.85, 1.28][depth] * (.78 + unit() * .4);
      const brightness = .48 + unit() * .32;
      element('path', {
        d, stroke: unit() < .5 ? '#88beef' : '#b5d2ee', 'stroke-width': (widthAtDepth * (3.1 + unit() * 1.3)).toFixed(2),
        opacity: (brightness * .19).toFixed(3)
      }, aura);
      element('path', {
        d, stroke: '#607f9b', 'stroke-width': widthAtDepth.toFixed(2), opacity: (brightness * .7).toFixed(3)
      }, body);
      for (let segment = 0; segment < edge.length - 1; segment++) {
        const detail = pathData(edge.slice(segment, segment + 2));
        element('path', {
          d: detail, stroke: unit() < .5 ? '#3d739e' : '#a4c5df',
          'stroke-width': (widthAtDepth * (.75 + unit() * .4)).toFixed(2),
          opacity: (brightness * (.13 + unit() * .23)).toFixed(3)
        }, body);
        if (unit() < .48) element('path', {
          d: detail, stroke: unit() < .5 ? '#f3fbff' : '#b8dcf5',
          'stroke-width': (widthAtDepth * (.17 + unit() * .13)).toFixed(2),
          opacity: (brightness * (.24 + unit() * .4)).toFixed(3)
        }, shine);
      }
    }
    for (const id of selectedIds(leaf)) pageRoute.push(...edges[id].slice(1));
    layout.push({root, target, leaf, spread: baseSpread});

    if (treeIndex < 2) {
      const nextRoot = roots[treeIndex + 1];
      pageRoute.push(...jaggedEdge(target, nextRoot, 4, 15).slice(1));
    }
  }

  const d = pathData(pageRoute);
  for (const id of ['path-blur', 'path-glow', 'path-core']) {
    const path = $('#' + id);
    path.setAttribute('d', d);
    boltLength = path.getTotalLength();
    path.style.strokeDasharray = `${boltLength} ${boltLength}`;
    path.style.strokeDashoffset = `${boltLength}`;
  }
  return true;
}

function strike(now) {
  if (!newStrike()) { nextStrike = now + 150; return; }
  lastStrike = now;
  nextStrike = now + nextIntervalMs();
}

function render(now) {
  if (paused) return;
  if (now >= nextStrike) strike(now);
  const age = now - lastStrike;
  const fade = age < 0 ? 0 : age < BOLT_HOLD_MS ? 1 : clamp(1 - (age - BOLT_HOLD_MS) / BOLT_FADE_MS);
  const arrival = clamp(age / BOLT_ARRIVAL_MS);
  const visible = fade * clamp(age / 130);
  const sweep = 1 - (1 - arrival) ** 2;
  const offset = boltLength * (1 - sweep);
  for (const id of ['path-blur', 'path-glow', 'path-core']) $('#' + id).style.strokeDashoffset = `${offset}`;
  treeGroups.forEach((group, index) => {
    const reveal = clamp((age - index * 110) / 170);
    group.setAttribute('opacity', reveal.toFixed(3));
  });
  $('#sky-glow').setAttribute('opacity', (visible * .38).toFixed(3));
  $('#energy').setAttribute('opacity', visible.toFixed(3));
  $('#trees').setAttribute('opacity', visible.toFixed(3));
  requestAnimationFrame(render);
}

function responsive() {
  if (pageRoute.length) requestAnimationFrame(newStrike);
}

responsive();
addEventListener('resize', responsive);
$('#zeus-full').addEventListener('load', responsive);
if (!paused) requestAnimationFrame(render);

window.zeusStudy = {
  strike: () => strike(performance.now()),
  get layout() { return layout; },
  get pageRoute() { return pageRoute; },
  get hand() { return pageHand; },
  pause() { paused = true; },
  resume() { if (paused) { paused = false; requestAnimationFrame(render); } }
};
