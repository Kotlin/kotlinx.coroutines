import unittest

from analyze_trace import analyze_trace, union_duration


def span(span_id, start, duration, parent=None):
    return {
        "traceID": "trace", "spanID": span_id, "operationName": span_id,
        "startTime": start, "duration": duration, "processID": "p1",
        "references": [] if parent is None else [{"refType": "CHILD_OF", "traceID": "trace", "spanID": parent}],
        "tags": [],
    }


class IntervalTest(unittest.TestCase):
    def test_nested_and_overlapping_intervals_are_not_added(self):
        self.assertEqual(15, union_duration([(0, 10), (2, 5), (8, 15)]))

    def test_disjoint_touching_and_empty_intervals(self):
        self.assertEqual(10, union_duration([(0, 5), (5, 8), (12, 14), (20, 20)]))
        self.assertEqual(0, union_duration([]))

    def test_clipping_and_outside_intervals(self):
        self.assertEqual(5, union_duration([(-10, 3), (7, 20), (30, 40)], clip=(0, 9)))

    def test_reversed_interval_is_invalid(self):
        with self.assertRaises(ValueError):
            union_duration([(3, 2)])


class TraceTest(unittest.TestCase):
    def analyze(self, spans):
        return analyze_trace({"traceID": "trace", "spans": spans, "processes": {"p1": {"serviceName": "example"}}})

    def test_direct_child_union_excludes_grandchild_double_counting(self):
        result = self.analyze([span("root", 0, 10000), span("a", 1000, 6000, "root"),
                               span("b", 5000, 3000, "root"), span("c", 2000, 1000, "a")])
        root = next(s for s in result["spans"] if s["spanID"] == "root")
        self.assertEqual(7, root["direct_child_union_ms"])
        self.assertEqual(3, root["uncovered_by_direct_children_ms"])
        self.assertEqual(["root"], result["root_span_ids"])

    def test_out_of_parent_child_is_clipped_and_reported(self):
        result = self.analyze([span("root", 1000, 3000), span("child", 0, 5000, "root")])
        root = next(s for s in result["spans"] if s["spanID"] == "root")
        self.assertEqual(3, root["direct_child_union_ms"])
        self.assertEqual(0, root["uncovered_by_direct_children_ms"])
        self.assertEqual([{"spanID": "child", "parentID": "root"}], result["out_of_parent_bounds"])

    def test_missing_and_cross_trace_parent_are_not_local_roots(self):
        child = span("cross", 0, 10, "remote")
        child["references"][0]["traceID"] = "another-trace"
        result = self.analyze([span("orphan", 0, 10, "missing"), child])
        self.assertEqual([], result["root_span_ids"])
        self.assertEqual(1, len(result["missing_same_trace_parents"]))
        self.assertEqual(1, len(result["cross_trace_parents"]))

    def test_empty_trace_has_unknown_duration(self):
        result = self.analyze([])
        self.assertIsNone(result["envelope_ms"])
        self.assertEqual([], result["operations"])

    def test_negative_duration_and_duplicate_ids_are_rejected(self):
        with self.assertRaises(ValueError):
            self.analyze([span("a", 0, -1)])
        with self.assertRaises(ValueError):
            self.analyze([span("a", 0, 1), span("a", 1, 1)])

    def test_embedded_reference_span_is_not_counted_or_copied(self):
        child = span("child", 1, 1, "root")
        child["references"][0]["span"] = span("root", 0, 10)
        result = self.analyze([span("root", 0, 10), child])
        self.assertEqual(2, result["span_count"])
        self.assertNotIn("span", result["spans"][1]["references"][0])

    def test_http_repetition_is_method_sensitive(self):
        requests = []
        for index, method in enumerate(("HEAD", "HEAD", "GET")):
            request = span(str(index), index * 1000, 1000)
            request["operationName"] = method
            request["tags"] = [{"key": "url.full", "value": "https://example.test/a"},
                               {"key": "http.response.status_code", "value": 200}]
            requests.append(request)
        http = self.analyze(requests)["http"]
        self.assertEqual(3, http["count"])
        self.assertEqual(3, http["interval_union_ms"])
        self.assertEqual(1, http["repeated_method_url_count"])
        self.assertEqual(1, http["extra_identical_method_url_occurrences"])


if __name__ == "__main__":
    unittest.main()