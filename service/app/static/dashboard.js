(function () {
  'use strict';

  function attachChart(svg, tip, points) {
    if (!svg || !tip) return;
    var cross = svg.querySelector('.crosshair');
    var plot = svg.closest('.chart-plot');
    function fmt(n) { return Number(n).toLocaleString('en-US'); }
    function hideTip() { tip.hidden = true; if (cross) cross.setAttribute('visibility', 'hidden'); }
    function showPoint(point) {
      if (cross) { cross.setAttribute('x1', point.x); cross.setAttribute('x2', point.x); cross.setAttribute('visibility', 'visible'); }
      tip.textContent = '';
      var head = document.createElement('strong');
      head.textContent = fmt(point.value) + ' = ' + fmt(point.sigma) + ' B × ' + fmt(point.hverify);
      tip.appendChild(head); tip.appendChild(document.createElement('br'));
      var line = point.login + (point.date ? ' · ' + point.date : '') + (point.frontier ? ' · frontier' : '') + (point.demo ? ' · demo' : '');
      tip.appendChild(document.createTextNode(line));
      tip.hidden = false;
      var bounds = svg.getBoundingClientRect(), box = svg.viewBox.baseVal;
      var container = tip.parentElement.getBoundingClientRect();
      var x = bounds.left - container.left + point.x / box.width * bounds.width;
      var y = bounds.top - container.top + point.y / box.height * bounds.height;
      tip.style.left = Math.max(4, Math.min(x + 12, container.width - tip.offsetWidth - 8)) + 'px';
      tip.style.top = Math.max(4, y - tip.offsetHeight - 12) + 'px';
    }
    svg.addEventListener('pointermove', function (event) {
      if (!points.length || event.pointerType === 'touch') return;
      var p = svg.createSVGPoint(); p.x = event.clientX; p.y = event.clientY;
      var mouse = p.matrixTransform(svg.getScreenCTM().inverse()), best, distance = Infinity;
      points.forEach(function (point) {
        var d = Math.hypot(point.x - mouse.x, point.y - mouse.y);
        if (d < distance) { distance = d; best = point; }
      });
      if (distance < 45) showPoint(best); else hideTip();
    });
    svg.addEventListener('pointerleave', hideTip);
    if (plot) plot.addEventListener('scroll', hideTip);
    window.addEventListener('resize', hideTip);
    document.addEventListener('keydown', function (event) { if (event.key === 'Escape') hideTip(); });
    svg.querySelectorAll('.chart-record').forEach(function (link) {
      link.addEventListener('focus', function () { showPoint(points[+link.dataset.point]); });
      link.addEventListener('blur', hideTip);
      link.addEventListener('pointerdown', function (event) {
        if (event.pointerType === 'touch') showPoint(points[+link.dataset.point]);
      });
    });
  }
  function readPoints(id) {
    var node = document.getElementById(id);
    try { return node ? JSON.parse(node.textContent) : []; } catch (error) { return []; }
  }
  attachChart(document.querySelector('svg.record-chart'), document.getElementById('tooltip-record'), readPoints('chart-points'));
  attachChart(document.querySelector('svg.pareto-chart'), document.getElementById('tooltip-pareto'), readPoints('pareto-points'));

  var buttons = document.querySelectorAll('.seg-btn');
  var views = document.querySelectorAll('.board-view');
  function show(view, updateUrl) {
    buttons.forEach(function (button) { button.setAttribute('aria-pressed', String(button.dataset.view === view)); });
    views.forEach(function (panel) { panel.hidden = panel.dataset.view !== view; });
    if (updateUrl) history.replaceState(null, '', location.pathname + location.search + '#' + view);
  }
  buttons.forEach(function (button) { button.addEventListener('click', function () { show(button.dataset.view, true); }); });
  function fromHash() {
    var view = location.hash === '#pareto' ? 'pareto' : 'spacetime';
    show(view, false);
    if (location.hash === '#pareto' || location.hash === '#spacetime') {
      var title = document.getElementById('board-title');
      if (title) title.scrollIntoView();
    }
  }
  window.addEventListener('hashchange', fromHash);
  fromHash();

  document.querySelectorAll('.lb-table').forEach(function (table) {
    var body = table.querySelector('tbody');
    table.querySelectorAll('.sort-btn').forEach(function (button) {
      button.addEventListener('click', function () {
        var key = button.dataset.key, direction = button.dataset.dir;
        if (button.getAttribute('aria-pressed') === 'true') {
          direction = direction === 'asc' ? 'desc' : 'asc'; button.dataset.dir = direction;
        }
        table.querySelectorAll('.sort-btn').forEach(function (other) {
          other.setAttribute('aria-pressed', String(other === button));
          other.parentNode.setAttribute('aria-sort', other === button ? (direction === 'asc' ? 'ascending' : 'descending') : 'none');
        });
        var rows = Array.prototype.slice.call(body.querySelectorAll('tr.lb-row'));
        rows.sort(function (a, b) {
          var va = a.dataset[key], vb = b.dataset[key];
          if (va === '' && vb === '') return 0; if (va === '') return 1; if (vb === '') return -1;
          if (key !== 'date') { va = Number(va); vb = Number(vb); }
          return (va < vb ? -1 : va > vb ? 1 : 0) * (direction === 'asc' ? 1 : -1);
        });
        rows.forEach(function (row) { body.appendChild(row); });
      });
    });
  });
})();
