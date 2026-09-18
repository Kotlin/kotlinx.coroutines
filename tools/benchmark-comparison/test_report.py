"""Run with python3 tools/benchmark-comparison/test_report.py (requires agent-browser)."""

import json
import math
import statistics
import subprocess
import unittest

from generate import OUTPUT, RESULTS, read_result, render


SESSION = "benchmark-comparison"


def browser(*args):
    return subprocess.check_output(
        ["agent-browser", "--session", SESSION, *args], text=True
    ).strip()


def evaluate(script):
    return json.loads(browser("eval", script))


class ComparisonTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = {side: read_result(RESULTS / side / "benchmark.html")
                    for side in ("baseline", "lookahead-deps-full")}
        browser("open", OUTPUT.as_uri())

    @classmethod
    def tearDownClass(cls):
        browser("close")

    def setUp(self):
        evaluate('$("metric").value="total execution time"; $("stat").value="median"; '
                 '$("filter").value="all"; $("sort").value="original"; '
                 '$("search").value=""; selected=null; $("detail").hidden=true; render(); true')

    def test_generated_data_matches_sources(self):
        self.assertEqual(OUTPUT.read_text(encoding="utf-8"), render())
        self.assertEqual(evaluate("data"), self.data)
        self.assertEqual(evaluate("names.length"), 9)
        self.assertEqual(evaluate('document.querySelectorAll("#rows tr").length'), 9)
        self.assertEqual(evaluate('document.querySelectorAll("script[src],link[rel=stylesheet]").length'), 0)

    def test_every_statistic_against_python(self):
        actual = evaluate('names.flatMap(name => metrics.flatMap(metric => '
                          '["median","mean"].map(stat => ({metric,stat,...compare(name,metric,stat)}))))')
        source_maps = [{s["definition"]["name"]: s for s in report["scenarios"]}
                       for report in self.data.values()]
        for row in actual:
            expected = []
            for side, key in zip(source_maps, ("a", "b")):
                samples = [i["values"][row["metric"]] for i in side[row["name"]]["iterations"]
                           if i["phase"] == "MEASURE"]
                if not samples:
                    self.assertIsNone(row[key])
                    expected.append(None)
                    continue
                value = getattr(statistics, row["stat"])(samples)
                expected.append(value)
                self.assertAlmostEqual(row[key]["value"], value)
                self.assertAlmostEqual(row[key]["sd"], statistics.stdev(samples))
                self.assertEqual(row[key]["n"], 3)
                self.assertEqual(row[key]["min"], min(samples))
                self.assertEqual(row[key]["max"], max(samples))
            if None in expected:
                self.assertIsNone(row["change"])
                self.assertIsNone(row["saved"])
            else:
                a, b = expected
                self.assertAlmostEqual(row["change"], (b / a - 1) * 100)
                self.assertAlmostEqual(row["saved"], a - b)
        totals = [r for r in actual if r["metric"] == "total execution time"
                  and r["stat"] == "median" and r["change"] is not None]
        geo = (math.exp(statistics.mean(math.log(r["b"]["value"] / r["a"]["value"])
                                        for r in totals)) - 1) * 100
        self.assertEqual(evaluate('document.querySelector("#cards strong").textContent'), f"{geo:+.1f}%")
        self.assertEqual(sum(r["change"] < 0 for r in totals), 5)

    def test_summary_edge_cases(self):
        self.assertIsNone(evaluate('summarize([], "median")'))
        self.assertEqual(evaluate('summarize([4,1,3,2], "median").value'), 2.5)
        self.assertIsNone(evaluate('summarize([2], "mean").sd'))
        self.assertEqual(evaluate('values({iterations:[{phase:"WARM_UP",values:{x:999}},'
                                  '{phase:"MEASURE",values:{x:0}},'
                                  '{phase:"MEASURE",values:{}}]}, "x")'), [0])
        self.assertEqual(evaluate('esc("<script>&")'), "&lt;script&gt;&amp;")

    def test_filters_sort_and_search(self):
        for option, count in (("good", 5), ("bad", 3), ("missing", 1)):
            browser("select", "#filter", option)
            self.assertEqual(evaluate('document.querySelectorAll("#rows button").length'), count)
        browser("click", "#rows button")
        self.assertIn("No samples recorded", evaluate('$("detail").textContent'))
        browser("click", "#close-detail")
        self.assertTrue(evaluate('$("detail").hidden'))
        browser("select", "#filter", "all")
        for option, first in (("regression", "Core build script change"),
                              ("change", "Sync · warm / warm / cold"),
                              ("saved", "Fully cold sync")):
            browser("select", "#sort", option)
            self.assertIn(first, evaluate('document.querySelector("#rows button").textContent'))
        browser("fill", "#search", "buildSrc")
        self.assertEqual(evaluate('document.querySelectorAll("#rows button").length'), 1)
        browser("fill", "#search", "no-such-scenario")
        self.assertIn("No scenarios match", evaluate('$("rows").textContent'))

    def test_metric_statistic_and_drilldown(self):
        browser("select", "#stat", "mean")
        browser("select", "#metric", "Gradle total execution time")
        self.assertIn("1.221 s", evaluate('document.querySelector("#rows tr").textContent'))
        browser("click", "#rows button")
        self.assertFalse(evaluate('$("detail").hidden'))
        self.assertEqual(evaluate('document.querySelectorAll("#detail .warmup").length'), 2)
        self.assertEqual(evaluate('document.querySelectorAll("#detail .detail-grid tbody tr").length'), 8)
        self.assertIn("36.403", evaluate('$("detail").textContent'))
        browser("click", "#close-detail")
        self.assertTrue(evaluate('document.activeElement.matches("#rows button")'))

    def test_mobile_and_desktop_layout(self):
        for width in (390, 1440):
            browser("set", "viewport", str(width), "1000")
            self.assertTrue(evaluate('document.documentElement.scrollWidth <= innerWidth'))
            browser("click", "#rows button")
            self.assertTrue(evaluate('document.documentElement.scrollWidth <= innerWidth'))
            browser("click", "#close-detail")


if __name__ == "__main__":
    unittest.main(verbosity=2)