"""Record history and Pareto frontier as bounded, escaped SVG with a small JSON side channel."""
from __future__ import annotations

import json
import math
from datetime import datetime, timedelta
from html import escape

W, H = 960, 380
ML, MR, MT, MB = 92, 40, 30, 46


def fmt(v: int | float) -> str:
    return f"{int(v):,}"


def _nice_ticks(lo: float, hi: float) -> list[int]:
    target = max((hi - lo) / 6, 1)
    scale = 10 ** math.floor(math.log10(target))
    step = next(n * scale for n in (1, 2, 5, 10) if n * scale >= target)
    start = math.ceil(lo / step) * step
    return [int(v) for v in range(int(start), int(math.floor(hi)) + 1, int(step))]


def _time_ticks(t0: datetime, t1: datetime, n: int = 5) -> list[datetime]:
    span = (t1 - t0).total_seconds()
    return [t0 + timedelta(seconds=span * i / (n - 1)) for i in range(n)]


def record_chart(points: list[dict], now: datetime, unit: str = "spacetime") -> dict:
    """The best score over time as a step curve. Points carry t, value, id, login, sigma, hverify."""
    t1 = max([now, *(p["t"] for p in points)])
    t0 = min((p["t"] for p in points), default=now - timedelta(days=1))
    if t1 - t0 < timedelta(days=1):
        t0 = t1 - timedelta(days=1)
    t0 -= (t1 - t0) * 0.04
    tick_fmt = "%b %d %H:%M" if t1 - t0 < timedelta(days=3) else "%b %d"
    values = [p["value"] for p in points] or [1]
    y_lo, y_hi = 0, max(values) * 1.15
    if y_hi <= y_lo:
        y_hi = y_lo + 1

    def sx(t: datetime) -> float:
        return ML + (W - ML - MR) * (t - t0).total_seconds() / max((t1 - t0).total_seconds(), 1)

    def sy(v: float) -> float:
        return MT + (H - MT - MB) * (y_hi - v) / max(y_hi - y_lo, 1)

    out = [f'<svg viewBox="0 0 {W} {H}" class="record-chart" role="group" '
           'aria-labelledby="record-chart-title record-chart-desc">',
           '<title id="record-chart-title">Best spacetime over time</title>',
           '<desc id="record-chart-desc">Each step is a merged record that lowered signature bytes times '
           'verification work. Hover or focus a record for its solver.</desc>']
    for v in _nice_ticks(y_lo, y_hi):
        y = sy(v)
        out.append(f'<line class="grid" x1="{ML}" x2="{W - MR}" y1="{y:.1f}" y2="{y:.1f}"/>')
        out.append(f'<text class="tick" x="{ML - 8}" y="{y + 4:.1f}" text-anchor="end">{fmt(v)}</text>')
    out.append(f'<line class="axis" x1="{ML}" x2="{W - MR}" y1="{H - MB}" y2="{H - MB}"/>')
    for t in _time_ticks(t0, t1):
        out.append(f'<text class="tick" x="{sx(t):.1f}" y="{H - MB + 20}" text-anchor="middle">{t.strftime(tick_fmt)}</text>')
    out.append(f'<text class="tick" x="4" y="{MT - 14}">{escape(unit)}</text>')
    side = []
    if points:
        d = f'M{sx(points[0]["t"]):.1f},{sy(points[0]["value"]):.1f}'
        for p in points[1:]:
            d += f' H{sx(p["t"]):.1f} V{sy(p["value"]):.1f}'
        d += f' H{sx(t1):.1f}'
        out.append(f'<g class="chart-series"><path class="line" d="{d}"/>')
        for p in points:
            x, y = sx(p["t"]), sy(p["value"])
            side.append({"x": round(x, 1), "y": round(y, 1), "value": p["value"], "sigma": p["sigma"],
                         "hverify": p["hverify"], "login": p["login"], "id": p["id"],
                         "date": p["t"].strftime("%Y-%m-%d %H:%M UTC"), "demo": p.get("demo", False)})
            title = escape(f'{fmt(p["value"])} = {fmt(p["sigma"])} B × {fmt(p["hverify"])} · {p["login"]} · '
                           f'{side[-1]["date"]}' + (' · demo' if p.get("demo") else ''))
            out.append(f'<a href="/submissions/{escape(p["id"])}" class="chart-record" data-point="{len(side) - 1}" aria-label="{title}">'
                       f'<circle class="hit-area" cx="{x:.1f}" cy="{y:.1f}" r="16"/>'
                       f'<circle class="mark" cx="{x:.1f}" cy="{y:.1f}" r="4.5"><title>{title}</title></circle></a>')
        out.append('</g>')
    else:
        out.append(f'<text class="tick empty" x="{(ML + W - MR) / 2:.1f}" y="{(MT + H - MB) / 2:.1f}" text-anchor="middle">No merged record yet</text>')
    out.append(f'<line class="crosshair" x1="0" x2="0" y1="{MT}" y2="{H - MB}" visibility="hidden"/>')
    out.append('</svg>')
    return {"svg": '\n'.join(out), "points": json.dumps(side).replace('<', '\\u003c')}


PW, PH = 960, 420
PML, PMR, PMT, PMB = 92, 40, 30, 56


def pareto_chart(records: list, frontier_ids: set[str]) -> dict:
    """Signature bytes against verification work for every record; frontier points are joined."""
    pts = [{"sigma": s.sigma, "hverify": s.hverify, "id": s.id, "login": s.user.login, "value": s.score_int,
            "frontier": s.id in frontier_ids, "demo": bool(s.detail_dict.get("demo"))} for s in records]
    xs = [p["sigma"] for p in pts] or [1]
    ys = [p["hverify"] for p in pts] or [1]
    x_hi, y_hi = max(xs) * 1.15, max(ys) * 1.15

    def sx(v: float) -> float:
        return PML + (PW - PML - PMR) * v / max(x_hi, 1)

    def sy(v: float) -> float:
        return PMT + (PH - PMT - PMB) * (y_hi - v) / max(y_hi, 1)

    out = [f'<svg viewBox="0 0 {PW} {PH}" class="pareto-chart" role="group" '
           'aria-labelledby="pareto-chart-title pareto-chart-desc">',
           '<title id="pareto-chart-title">Pareto frontier</title>',
           '<desc id="pareto-chart-desc">Signature bytes on the horizontal axis, verification work on the vertical '
           'axis. Filled marks are frontier records that no other record beats on both.</desc>']
    for v in _nice_ticks(0, y_hi):
        y = sy(v)
        out.append(f'<line class="grid" x1="{PML}" x2="{PW - PMR}" y1="{y:.1f}" y2="{y:.1f}"/>')
        out.append(f'<text class="tick" x="{PML - 8}" y="{y + 4:.1f}" text-anchor="end">{fmt(v)}</text>')
    for v in _nice_ticks(0, x_hi):
        x = sx(v)
        out.append(f'<text class="tick" x="{x:.1f}" y="{PH - PMB + 20}" text-anchor="middle">{fmt(v)}</text>')
    out.append(f'<line class="axis" x1="{PML}" x2="{PW - PMR}" y1="{PH - PMB}" y2="{PH - PMB}"/>')
    out.append(f'<text class="tick" x="4" y="{PMT - 14}">verification work (hash-work units)</text>')
    out.append(f'<text class="tick" x="{PW - PMR}" y="{PH - 10}" text-anchor="end">signature bytes</text>')
    front = sorted((p for p in pts if p["frontier"]), key=lambda p: p["sigma"])
    if front:
        d = f'M{sx(front[0]["sigma"]):.1f},{sy(front[0]["hverify"]):.1f}'
        for p in front[1:]:
            d += f' H{sx(p["sigma"]):.1f} V{sy(p["hverify"]):.1f}'
        out.append(f'<path class="frontier" d="{d}"/>')
    side = []
    for p in pts:
        x, y = sx(p["sigma"]), sy(p["hverify"])
        side.append({"x": round(x, 1), "y": round(y, 1), **{k: p[k] for k in ("sigma", "hverify", "value", "login", "id", "frontier", "demo")}})
        title = escape(f'{fmt(p["sigma"])} B × {fmt(p["hverify"])} = {fmt(p["value"])} · {p["login"]}'
                       + (' · frontier' if p["frontier"] else '') + (' · demo' if p["demo"] else ''))
        cls = "mark frontier" if p["frontier"] else "mark dominated"
        out.append(f'<a href="/submissions/{escape(p["id"])}" class="chart-record" data-point="{len(side) - 1}" aria-label="{title}">'
                   f'<circle class="hit-area" cx="{x:.1f}" cy="{y:.1f}" r="16"/>'
                   f'<circle class="{cls}" cx="{x:.1f}" cy="{y:.1f}" r="5"><title>{title}</title></circle></a>')
    if not pts:
        out.append(f'<text class="tick empty" x="{(PML + PW - PMR) / 2:.1f}" y="{(PMT + PH - PMB) / 2:.1f}" text-anchor="middle">No merged record yet</text>')
    out.append('</svg>')
    return {"svg": '\n'.join(out), "points": json.dumps(side).replace('<', '\\u003c')}
