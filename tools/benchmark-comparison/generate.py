"""Generate the offline comparison: python3 tools/benchmark-comparison/generate.py."""

import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "import-benchmarks/seb"
OUTPUT = RESULTS / "lookahead-deps-full-vs-baseline.html"


def read_result(path):
    text = path.read_text(encoding="utf-8")
    match = re.search(r"const benchmarkResult\s*=\s*", text)
    if not match:
        raise ValueError(f"No benchmarkResult in {path}")
    result, _ = json.JSONDecoder().raw_decode(text[match.end():])
    names = [s["definition"]["name"] for s in result["scenarios"]]
    if len(names) != len(set(names)):
        raise ValueError(f"Duplicate scenarios in {path}")
    for scenario in result["scenarios"]:
        for sample in scenario["samples"]:
            if sample["unit"] != "ms":
                raise ValueError(f"Unexpected unit in {path}: {sample}")
        for iteration in scenario["iterations"]:
            for value in iteration["values"].values():
                if not isinstance(value, (int, float)) or not 0 <= value < float("inf"):
                    raise ValueError(f"Invalid duration in {path}: {value}")
    return result


def render():
    data = {name: read_result(RESULTS / name / "benchmark.html")
            for name in ("baseline", "lookahead-deps-full")}
    # Escape HTML-sensitive characters, including any closing script tag in metadata.
    payload = json.dumps(data, separators=(",", ":"), allow_nan=False)
    payload = payload.replace("&", "\\u0026").replace("<", "\\u003c").replace(">", "\\u003e")
    template = Path(__file__).with_name("report.html").read_text(encoding="utf-8")
    return template.replace("__BENCHMARK_DATA__", payload)


if __name__ == "__main__":
    OUTPUT.write_text(render(), encoding="utf-8")
    print(OUTPUT.relative_to(ROOT))