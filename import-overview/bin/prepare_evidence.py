"""Copy existing benchmark evidence and extract its JSON; never run a benchmark.

Run from any directory with Python 3.9+: python3 import-overview/bin/prepare_evidence.py
Only the named files under this script's directory are written.
"""

import argparse
import hashlib
import json
import math
from pathlib import Path
import re
import shutil
import statistics
import subprocess


OUTPUT = Path(__file__).resolve().parent
ROOT = OUTPUT.parents[1]
DATASETS = ("baseline", "gradle-xxh3-hash", "lookahead-deps", "lookahead-deps-full")
INPUTS = (
    "performance.scenarios",
    "benchmark-idea-sync.sh",
    "benchmark-idea-sync-cold3.sh",
    "gradle/wrapper/gradle-wrapper.properties",
    "gradle.properties",
    "settings.gradle.kts",
    "build.gradle.kts",
    "buildSrc/build.gradle.kts",
    "kotlinx-coroutines-core/build.gradle.kts",
)


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n", encoding="utf-8")


def read_report(path):
    text = path.read_text(encoding="utf-8")
    match = re.search(r"const benchmarkResult\s*=\s*", text)
    if match is None:
        raise ValueError(f"Missing benchmarkResult: {path}")
    result, _ = json.JSONDecoder().raw_decode(text[match.end():])
    names = [scenario["definition"]["name"] for scenario in result["scenarios"]]
    if len(names) != len(set(names)):
        raise ValueError(f"Duplicate scenario: {path}")
    for scenario in result["scenarios"]:
        metrics = {sample["name"] for sample in scenario["samples"]}
        if any(sample["unit"] != "ms" for sample in scenario["samples"]):
            raise ValueError(f"Unexpected unit: {path}")
        for iteration in scenario["iterations"]:
            if iteration["phase"] not in ("MEASURE", "WARM_UP"):
                raise ValueError(f"Unexpected iteration phase: {path}")
            if set(iteration["values"]) != metrics:
                raise ValueError(f"Missing metric: {path}")
            for value in iteration["values"].values():
                if not isinstance(value, (int, float)) or not math.isfinite(value) or value < 0:
                    raise ValueError(f"Invalid duration: {path}")
    return result


def capture_sources():
    catalog = json.loads((OUTPUT / "source-locations.json").read_text(encoding="utf-8"))
    repositories = {}
    for name, repository in catalog["repositories"].items():
        root = repository["root"]
        revision = subprocess.check_output(["git", "-C", root, "rev-parse", "HEAD"], text=True).strip()
        if revision != repository["inspected_revision"]:
            raise ValueError(f"Source revision changed: {name}: {revision}")
        status = subprocess.check_output(["git", "-C", root, "status", "--porcelain=v1", "-uno"], text=True)
        repositories[name] = {**repository, "captured_revision": revision, "tracked_status": status.splitlines()}
    references = []
    for reference in catalog["references"]:
        relative_path = catalog["prefixes"][reference["prefix"]] + reference["path"]
        path = Path(repositories[reference["repository"]]["root"]) / relative_path
        data = path.read_bytes()
        lines = data.decode("utf-8").splitlines()
        excerpts = []
        for start, end in reference["ranges"]:
            if not 1 <= start <= end <= len(lines):
                raise ValueError(f"Invalid source range: {path}:{start}-{end}")
            excerpts.append({"start_line": start, "end_line": end, "lines": lines[start - 1:end]})
        references.append({**reference, "repository_relative_path": relative_path,
                           "file_sha256": hashlib.sha256(data).hexdigest(), "excerpts": excerpts})
    write_json(OUTPUT / "source-excerpts.json", {
        "schema_version": 1, "repositories": repositories, "references": references,
        "note": "Working-tree excerpts, not release binaries; tracked status excludes untracked files.",
    })
    print(f"Captured {len(references)} source references.")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--sources", action="store_true", help="Also archive source excerpts from the two local checkouts")
    options = parser.parse_args()
    # Parse all reports before writing; malformed inputs must not become zero timings.
    reports = {
        name: read_report(ROOT / "import-benchmarks/seb" / name / "benchmark.html")
        for name in DATASETS
    }
    manifest = []

    def preserve(relative_source, relative_destination):
        source = ROOT / relative_source
        destination = OUTPUT / relative_destination
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, destination)
        data = destination.read_bytes()
        manifest.append({
            "source": relative_source,
            "path": relative_destination,
            "bytes": len(data),
            "sha256": hashlib.sha256(data).hexdigest(),
        })

    summaries = []
    for name, report in reports.items():
        for filename in ("benchmark.html", "benchmark.csv", "profile.log"):
            preserve(f"import-benchmarks/seb/{name}/{filename}", f"benchmarks/{name}/{filename}")
        for scenario in report["scenarios"]:
            measurements = [i for i in scenario["iterations"] if i["phase"] == "MEASURE"]
            metrics = {}
            for sample in scenario["samples"]:
                values = [i["values"][sample["name"]] for i in measurements]
                metrics[sample["name"]] = {
                    "unit": sample["unit"],
                    "values": values,
                    "median": statistics.median(values) if values else None,
                    "min": min(values) if values else None,
                    "max": max(values) if values else None,
                }
            summaries.append({
                "dataset": name,
                "scenario": scenario["definition"]["name"],
                "gradle_version": scenario["definition"]["version"],
                "report_date": report["date"],
                "measurement_count": len(measurements),
                "status": "measured" if measurements else "no-measurements",
                "metrics": metrics,
            })
    for path in INPUTS:
        preserve(path, f"inputs/{path}")
    write_json(OUTPUT / "benchmark-results.json", {"schema_version": 1, "datasets": reports})
    write_json(OUTPUT / "measurement-summary.json", {
        "schema_version": 1,
        "aggregation": "Per-metric median/min/max; only MEASURE iterations; no pairing across datasets",
        "scenarios": summaries,
    })
    write_json(OUTPUT / "raw-file-manifest.json", {"schema_version": 1, "files": manifest})
    print(f"Preserved {len(manifest)} files; extracted {len(summaries)} scenario records.")
    if options.sources:
        capture_sources()


if __name__ == "__main__":
    main()