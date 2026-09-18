"""Generate benchmark-comparison.html: python3 tools/benchmark-comparison/compare_current.py."""

import json
from pathlib import Path

from generate import ROOT, read_result


OUTPUT = ROOT / "benchmark-comparison.html"
SOURCES = {
    "current": "benchmark-out/benchmark.html",
    **{name: f"import-benchmarks/seb/{name}/benchmark.html" for name in
       ("baseline", "gradle-xxh3-hash", "lookahead-deps", "lookahead-deps-full")},
}


def render():
    data = {name: {"path": path, **read_result(ROOT / path)}
            for name, path in SOURCES.items()}
    payload = json.dumps(data, separators=(",", ":"), allow_nan=False)
    payload = payload.replace("&", "\\u0026").replace("<", "\\u003c").replace(">", "\\u003e")
    template = Path(__file__).with_name("current-report.html").read_text(encoding="utf-8")
    return template.replace("__BENCHMARK_DATA__", payload)


if __name__ == "__main__":
    OUTPUT.write_text(render(), encoding="utf-8")
    print(OUTPUT.relative_to(ROOT))