"""Preserve the supplied Jaeger export and derive interval-based, non-CPU timings.

Run: python3 import-overview/bin/analyze_trace.py
No services are started and no source files are modified.
"""

from collections import defaultdict
from datetime import datetime, timedelta, timezone
import hashlib
import json
from pathlib import Path
import shutil


OUTPUT = Path(__file__).resolve().parent
ROOT = OUTPUT.parents[1]
SOURCE = ROOT / "import-benchmarks/yahor/traces-1789726526259.json"
DESTINATION = OUTPUT / "traces/yahor/traces-1789726526259.json"


def union_duration(intervals, clip=None):
    prepared = []
    for start, end in intervals:
        if end < start:
            raise ValueError("Reversed interval")
        if clip is not None:
            start, end = max(start, clip[0]), min(end, clip[1])
        if end > start:
            prepared.append((start, end))
    total = 0
    previous_end = None
    for start, end in sorted(prepared):
        if previous_end is None or start > previous_end:
            total += end - start
        elif end > previous_end:
            total += end - previous_end
        previous_end = max(end, previous_end) if previous_end is not None else end
    return total


def utc_time(microseconds):
    return (datetime(1970, 1, 1, tzinfo=timezone.utc) + timedelta(microseconds=microseconds)).isoformat()


def reference_ids(span):
    # Jaeger UI exports can embed ancestor objects; they are not additional spans.
    return [{key: reference[key] for key in ("refType", "traceID", "spanID")}
            for reference in span.get("references", [])]


def summarize_http(spans, intervals):
    requests = []
    by_method_url = defaultdict(list)
    for span in spans:
        if span["operationName"] not in ("GET", "HEAD"):
            continue
        tags = {tag["key"]: tag["value"] for tag in span.get("tags", [])}
        url = tags.get("url.full")
        request = {"spanID": span["spanID"], "method": span["operationName"], "url": url,
                   "status": tags.get("http.response.status_code"), "duration_ms": span["duration"] / 1000}
        requests.append(request)
        if url is not None:
            by_method_url[(request["method"], url)].append(request)
    repeated = [{"method": method, "url": url, "count": len(members), "requests": members}
                for (method, url), members in sorted(by_method_url.items()) if len(members) > 1]
    return {
        "scope": "Captured spans named GET/HEAD only; not all network work or inferred cache misses",
        "count": len(requests),
        "inclusive_sum_ms": sum(intervals[r["spanID"]][1] - intervals[r["spanID"]][0] for r in requests) / 1000,
        "interval_union_ms": union_duration([intervals[r["spanID"]] for r in requests]) / 1000,
        "repeated_method_url_count": len(repeated),
        "extra_identical_method_url_occurrences": sum(r["count"] - 1 for r in repeated),
        "repeated_method_urls": repeated,
        "requests": requests,
    }


def analyze_trace(trace):
    trace_id = trace["traceID"]
    spans = trace["spans"]
    by_id = {span["spanID"]: span for span in spans}
    if len(by_id) != len(spans):
        raise ValueError("Duplicate span ID")
    intervals = {}
    for span in spans:
        if span["traceID"] != trace_id:
            raise ValueError("Span belongs to another trace")
        for field in ("startTime", "duration"):
            if type(span[field]) is not int or span[field] < 0:
                raise ValueError(f"Invalid {field}")
        intervals[span["spanID"]] = (span["startTime"], span["startTime"] + span["duration"])
    start = min((i[0] for i in intervals.values()), default=None)
    end = max((i[1] for i in intervals.values()), default=None)
    children = defaultdict(list)
    missing_parents, cross_trace_parents, out_of_parent = [], [], []
    roots = []
    for span in spans:
        parents = [r for r in reference_ids(span) if r["refType"] == "CHILD_OF"]
        if not parents:
            roots.append(span["spanID"])
        for parent in parents:
            if parent["traceID"] != trace_id:
                cross_trace_parents.append({"spanID": span["spanID"], "reference": parent})
            elif parent["spanID"] not in by_id:
                missing_parents.append({"spanID": span["spanID"], "reference": parent})
            else:
                child_interval = intervals[span["spanID"]]
                parent_interval = intervals[parent["spanID"]]
                children[parent["spanID"]].append(child_interval)
                if child_interval[0] < parent_interval[0] or child_interval[1] > parent_interval[1]:
                    out_of_parent.append({"spanID": span["spanID"], "parentID": parent["spanID"]})
    normalized, groups = [], defaultdict(list)
    for span in sorted(spans, key=lambda s: (s["startTime"], -s["duration"], s["spanID"])):
        span_id = span["spanID"]
        tags = {tag["key"]: tag["value"] for tag in span.get("tags", [])}
        process = trace.get("processes", {}).get(span.get("processID"), {})
        coverage = union_duration(children[span_id], clip=intervals[span_id])
        normalized.append({
            "spanID": span_id,
            "operation": span["operationName"],
            "processID": span.get("processID"),
            "service": process.get("serviceName"),
            "thread_name": tags.get("thread.name"),
            "references": reference_ids(span),
            "start_unix_us": span["startTime"],
            "start_ms": (span["startTime"] - start) / 1000,
            "duration_ms": span["duration"] / 1000,
            "direct_child_union_ms": coverage / 1000,
            "uncovered_by_direct_children_ms": (span["duration"] - coverage) / 1000,
            "error_tag": tags.get("error") is True or tags.get("otel.status_code") == "ERROR",
            "tags": span.get("tags", []),
            "log_count": len(span.get("logs", [])),
            "warnings": span.get("warnings"),
        })
        groups[span["operationName"]].append(span)
    operation_summary = []
    for name, members in groups.items():
        operation_summary.append({
            "operation": name, "count": len(members),
            "inclusive_sum_ms": sum(s["duration"] for s in members) / 1000,
            "interval_union_ms": union_duration([intervals[s["spanID"]] for s in members]) / 1000,
            "max_ms": max(s["duration"] for s in members) / 1000,
        })
    return {
        "traceID": trace_id, "span_count": len(spans), "root_span_ids": roots,
        "start_utc": utc_time(start) if start is not None else None,
        "end_utc": utc_time(end) if end is not None else None,
        "envelope_ms": (end - start) / 1000 if spans else None,
        "processes": trace.get("processes", {}),
        "trace_warnings": trace.get("warnings"),
        "trace_errors_present": "errors" in trace,
        "trace_errors": trace.get("errors"),
        "missing_same_trace_parents": missing_parents,
        "cross_trace_parents": cross_trace_parents,
        "out_of_parent_bounds": out_of_parent,
        "error_tagged_span_count": sum(s["error_tag"] for s in normalized),
        "http": summarize_http(spans, intervals),
        "spans": normalized,
        "operations": sorted(operation_summary, key=lambda row: (-row["inclusive_sum_ms"], row["operation"])),
    }


def main():
    raw = SOURCE.read_bytes()
    export = json.loads(raw)
    analysis = {
        "schema_version": 1,
        "source": str(SOURCE.relative_to(ROOT)),
        "sha256": hashlib.sha256(raw).hexdigest(),
        "source_timestamp_unit": "us",
        "derived_duration_unit": "ms",
        "method": "Immediate CHILD_OF interval union clipped to parent; uncovered time is not CPU/self time. Nested span overlap is not thread concurrency.",
        "export_errors": export.get("errors"),
        "export_errors_present": "errors" in export,
        "traces": [analyze_trace(trace) for trace in export["data"]],
    }
    DESTINATION.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(SOURCE, DESTINATION)
    if DESTINATION.read_bytes() != raw:
        raise ValueError("Source changed while copying")
    (OUTPUT / "trace-analysis.json").write_text(json.dumps(analysis, indent=2, allow_nan=False) + "\n", encoding="utf-8")
    manifest = {
        "schema_version": 1, "source": analysis["source"],
        "path": str(DESTINATION.relative_to(OUTPUT)), "bytes": len(raw), "sha256": analysis["sha256"],
        "provenance": "User-supplied export; not a sync run by the documentation author",
    }
    (OUTPUT / "trace-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
    print(f"Preserved {len(raw)} bytes; analyzed {len(analysis['traces'])} traces and {sum(t['span_count'] for t in analysis['traces'])} spans.")


if __name__ == "__main__":
    main()