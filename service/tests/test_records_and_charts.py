"""Exact big-integer ranking, Pareto dominance, promotion rule, and bounded, escaped charts."""
from __future__ import annotations

import json
import unittest
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta
from types import SimpleNamespace

from app import charts, contract, records


def sub(sigma, hverify, ident=None, login='solver', at=None, demo=False):
    return SimpleNamespace(id=ident or f'{sigma}x{hverify}', sigma=sigma, hverify=hverify, score=str(sigma * hverify),
                           score_int=sigma * hverify, scored=True, record_at=at or datetime(2026, 9, 1),
                           finished_at=None, created_at=datetime(2026, 9, 1), user=SimpleNamespace(login=login),
                           detail_dict={'demo': demo})


class RecordsTests(unittest.TestCase):
    def test_ranking_orders_exact_products_beyond_64_bits(self):
        huge = sub(2 ** 62, 2 ** 62, 'huge')
        small = sub(2274, 160, 'small')
        tie_smaller_sig = sub(1137, 320, 'tie')          # same product as small, fewer bytes
        ranking = records.by_score([huge, small, tie_smaller_sig])
        self.assertEqual([s.id for s in ranking], ['tie', 'small', 'huge'])
        self.assertEqual(huge.score_int, 2 ** 124)

    def test_pareto_keeps_non_dominated_records_sorted_by_signature_bytes(self):
        recs = [sub(2000, 200), sub(1500, 300), sub(2100, 210), sub(3000, 100), sub(2000, 200, 'dup',
                                                                              at=datetime(2026, 9, 2))]
        front = records.pareto(recs)
        self.assertEqual([(s.sigma, s.hverify) for s in front], [(1500, 300), (2000, 200), (3000, 100)])
        self.assertEqual(front[1].id, '2000x200')       # the earlier of exact duplicates

    def test_promotion_rule_matches_the_spec(self):
        existing = [sub(2000, 200), sub(1500, 300)]
        self.assertTrue(records.improves([], 5000, 5000))                 # first record
        self.assertTrue(records.improves(existing, 1900, 190))            # better product
        self.assertTrue(records.improves(existing, 1000, 500))            # worse product, new frontier corner
        self.assertFalse(records.improves(existing, 2100, 210))           # dominated by (2000, 200)
        self.assertFalse(records.improves(existing, 2000, 200))           # duplicate
        self.assertFalse(records.improves(existing, 1500, 300))           # duplicate frontier point

    def test_lead_compares_score_then_signature(self):
        self.assertTrue(contract.leads(10, 5, None, None))
        self.assertTrue(contract.leads(10, 5, 11, 1))
        self.assertTrue(contract.leads(10, 5, 10, 6))
        self.assertFalse(contract.leads(10, 5, 10, 5))
        self.assertFalse(contract.leads(10, 5, 9, 9))

    def test_gains_are_relative_to_the_best_score_before_each_record(self):
        recs = [sub(2000, 200, 'a', at=datetime(2026, 9, 1)), sub(1000, 300, 'b', at=datetime(2026, 9, 2)),
                sub(500, 500, 'c', at=datetime(2026, 9, 3)), sub(3000, 90, 'd', at=datetime(2026, 9, 4)),
                sub(2200, 100, 'e', at=datetime(2026, 9, 5))]
        gains = records.gains(recs)
        self.assertIsNone(gains['a'])                    # first record
        self.assertEqual(gains['b'], 25.0)               # 400,000 -> 300,000
        self.assertEqual(gains['c'], 16.67)              # 300,000 -> 250,000
        self.assertIsNone(gains['d'])                    # 270,000: entered through the frontier, not the score
        self.assertEqual(gains['e'], 12.0)               # 250,000 -> 220,000


class ChartTests(unittest.TestCase):
    @staticmethod
    def point(value=363840, login='solver', ident='id', demo=False, t=None):
        return {'t': t or datetime(2026, 1, 1), 'value': value, 'sigma': 2274, 'hverify': 160,
                'login': login, 'id': ident, 'demo': demo}

    def test_record_chart_axis_is_bounded_for_huge_scores(self):
        for value in (1, 363_840, 5_224_364, 10 ** 13):
            with self.subTest(value=value):
                chart = charts.record_chart([self.point(value)], datetime(2026, 1, 2))
                svg = ET.fromstring(chart['svg'])
                self.assertLessEqual(len(svg.findall("./text[@class='tick']")), 16)
                self.assertLess(len(chart['svg']), 8000)

    def test_attribution_cannot_escape_svg_or_json_script(self):
        login = '</script><script>alert("x")</script>'
        chart = charts.record_chart([self.point(login=login, ident='a" onload="bad', demo=True)], datetime(2026, 1, 2))
        svg = ET.fromstring(chart['svg'])
        self.assertEqual(svg.findall('.//script'), [])
        self.assertNotIn('<', chart['points'])
        self.assertEqual(json.loads(chart['points'])[0]['login'], login)
        link = svg.find('.//a')
        self.assertIn(login, link.get('aria-label'))
        self.assertIn(' · demo', link.get('aria-label'))
        self.assertNotIn('onload', link.attrib)

    def test_empty_boards_render_a_placeholder_not_a_fake_point(self):
        chart = charts.record_chart([], datetime(2026, 1, 1))
        self.assertIn('No record yet', chart['svg'])
        self.assertEqual(json.loads(chart['points']), [])
        pareto = charts.pareto_chart([], set())
        self.assertIn('No record yet', pareto['svg'])

    def test_pareto_chart_marks_frontier_and_dominated_points_differently(self):
        recs = [sub(2000, 200, 'a'), sub(1500, 300, 'b'), sub(2100, 210, 'c')]
        chart = charts.pareto_chart(recs, {'a', 'b'})
        svg = ET.fromstring(chart['svg'])
        classes = [c.get('class') for c in svg.iter('circle') if c.get('class') != 'hit-area']
        self.assertEqual(classes.count('mark frontier'), 2)
        self.assertEqual(classes.count('mark dominated'), 1)
        self.assertIsNotNone(svg.find(".//path[@class='frontier']"))
        points = json.loads(chart['points'])
        self.assertEqual({p['id'] for p in points if p['frontier']}, {'a', 'b'})

    def test_future_timestamp_is_inside_chart_axis(self):
        now = datetime(2026, 1, 1)
        chart = charts.record_chart([self.point(t=now + timedelta(minutes=2))], now)
        svg = ET.fromstring(chart['svg'])
        axis_right = float(svg.find("./line[@class='axis']").get('x2'))
        self.assertLessEqual(json.loads(chart['points'])[0]['x'], axis_right)


if __name__ == '__main__':
    unittest.main()
