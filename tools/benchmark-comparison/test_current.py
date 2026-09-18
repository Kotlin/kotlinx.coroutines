"""Run: python3 tools/benchmark-comparison/test_current.py (requires agent-browser)."""

import json
import math
import statistics
import subprocess
import unittest

from compare_current import OUTPUT, ROOT, SOURCES, read_result, render


def browser(*args):
    return subprocess.check_output(
        ["agent-browser", "--session", "current-benchmark-comparison", *args], text=True
    ).strip()


def evaluate(script):
    return json.loads(browser("eval", script))


class CurrentComparisonTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.data = {key: {"path": path, **read_result(ROOT / path)} for key, path in SOURCES.items()}
        browser("open", OUTPUT.as_uri())

    @classmethod
    def tearDownClass(cls):
        browser("close")

    def setUp(self):
        evaluate('$("previous").value="lookahead-deps-full"; $("metric").value="total execution time"; '
                 '$("stat").value="median"; $("search").value=""; render(); true')

    def test_sources_and_offline_report(self):
        self.assertEqual(OUTPUT.read_text(encoding="utf-8"), render())
        self.assertEqual(evaluate("data"), self.data)
        self.assertEqual(evaluate('document.querySelectorAll("#rows tr").length'), 9)
        self.assertEqual(evaluate('document.querySelectorAll("#sources tr").length'), 5)
        self.assertEqual(evaluate('document.querySelectorAll("script[src],link[rel=stylesheet]").length'), 0)
        for path in evaluate('Array.from(document.querySelectorAll("a[href]")).map(a=>a.getAttribute("href"))'):
            self.assertTrue((ROOT / path).is_file(), path)
        self.assertEqual(browser("errors"), "")

    def test_all_calculations_against_python(self):
        actual = evaluate('history.flatMap(previous => names.flatMap(name => metrics.flatMap(metric => '
                          '["median","mean"].map(stat => ({previous,metric,stat,...compare(name,previous,metric,stat)})))))')
        maps = {key: {s["definition"]["name"]: s for s in report["scenarios"]}
                for key, report in self.data.items()}
        for row in actual:
            expected = []
            for side, field in ((row["previous"], "a"), ("current", "b")):
                scenario = maps[side].get(row["name"], {})
                samples = [i["values"][row["metric"]] for i in scenario.get("iterations", [])
                           if i["phase"] == "MEASURE" and row["metric"] in i["values"]]
                if not samples:
                    self.assertIsNone(row[field])
                    expected.append(None)
                    continue
                value = getattr(statistics, row["stat"])(samples)
                expected.append(value)
                self.assertAlmostEqual(row[field]["value"], value)
                self.assertEqual(row[field]["n"], len(samples))
                self.assertEqual(row[field]["min"], min(samples))
                self.assertEqual(row[field]["max"], max(samples))
            a, b = expected
            if a is None or b is None:
                self.assertIsNone(row["change"])
                self.assertIsNone(row["saved"])
            else:
                self.assertAlmostEqual(row["change"], (b / a - 1) * 100)
                self.assertAlmostEqual(row["saved"], a - b)
        for previous in SOURCES.keys() - {"current"}:
            browser("select", "#previous", previous)
            rows = [r for r in actual if r["previous"] == previous and r["stat"] == "median"
                    and r["metric"] == "total execution time" and r["change"] is not None]
            geo = (math.exp(statistics.mean(math.log(r["b"]["value"] / r["a"]["value"])
                                            for r in rows)) - 1) * 100
            self.assertEqual(evaluate('document.querySelector("#cards strong").textContent'), f"{geo:+.1f}%")

    def test_controls_and_raw_data(self):
        browser("select", "#previous", "gradle-xxh3-hash")
        self.assertIn("1 / 9", evaluate('$("cards").textContent'))
        self.assertIn("Not recorded", evaluate('$("rows").textContent'))
        browser("select", "#previous", "baseline")
        browser("select", "#metric", "Gradle total execution time")
        browser("select", "#stat", "mean")
        self.assertIn("1.129 s", evaluate('document.querySelector("#rows tr").textContent'))
        cards = evaluate('$("cards").textContent')
        browser("fill", "#search", "buildSrc")
        self.assertEqual(evaluate('document.querySelectorAll("#rows tr").length'), 1)
        self.assertEqual(evaluate('$("cards").textContent'), cards)
        browser("click", "#details summary")
        self.assertTrue(evaluate('document.querySelector("#details details").open'))
        self.assertEqual(evaluate('document.querySelectorAll("#details tbody tr").length'), 6)
        self.assertEqual(evaluate('document.querySelectorAll("#details .warmup").length'), 2)
        self.assertNotIn("undefined", evaluate('$("details").textContent'))
        browser("fill", "#search", "Gson")
        self.assertIn("No measured samples", evaluate('$("rows").textContent'))
        self.assertIn("No samples recorded", evaluate('$("details").textContent'))
        browser("fill", "#search", "no-matching-scenario")
        self.assertIn("No scenarios match", evaluate('$("rows").textContent'))

    def test_empty_zero_and_even_samples(self):
        self.assertIsNone(evaluate('summarize([], "median")'))
        self.assertEqual(evaluate('summarize([4,1,3,2], "median").value'), 2.5)
        self.assertEqual(evaluate('summarize([0], "mean").value'), 0)
        self.assertEqual(evaluate('values({iterations:[{phase:"WARM_UP",values:{x:999}},'
                                  '{phase:"MEASURE",values:{x:0}},{phase:"MEASURE",values:{}}]},"x")'), [0])
        self.assertEqual(evaluate('esc("<script>&")'), "&lt;script&gt;&amp;")
        self.assertIsNone(evaluate('(() => {const s=maps.baseline.get(names[0]); '
                                  'const old=s.iterations; try {s.iterations=[{phase:"MEASURE",values:{x:0}}]; '
                                  'return compare(names[0],"baseline","x","median").change;} '
                                  'finally {s.iterations=old;}})()'))

    def test_mobile_and_desktop_layout(self):
        for width in (390, 1440):
            browser("set", "viewport", str(width), "1000")
            self.assertTrue(evaluate('document.documentElement.scrollWidth <= innerWidth'))
            browser("click", "#details summary")
            self.assertTrue(evaluate('document.documentElement.scrollWidth <= innerWidth'))
            browser("click", "#environment summary")
            self.assertTrue(evaluate('document.documentElement.scrollWidth <= innerWidth'))


if __name__ == "__main__":
    unittest.main(verbosity=2)