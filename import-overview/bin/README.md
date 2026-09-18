# Raw evidence and machine-readable data

[Overview](../index.md) · [Results](../measurements/existing-results.md) · [Source map](../reference/sources.md)

`bin` means the evidence store here, not just executable binaries. Existing samples and the **user-supplied Jaeger export** are preserved without rewriting their source files. No new sync or telemetry capture was run by the documentation author.

## Contents

| Path | Kind / use |
| --- | --- |
| `benchmarks/<dataset>/benchmark.html` | Original report; embedded `const benchmarkResult` is the canonical structured data used here |
| `benchmarks/<dataset>/benchmark.csv` | Original CSV, including malformed row widths; retained for provenance, not parsed for statistics |
| `benchmarks/<dataset>/profile.log` | Original execution log, including failures and preparation outside measured intervals |
| `inputs/` | Copies of current scenarios, helper scripts and build configuration; not asserted historical inputs |
| [raw-file-manifest.json](raw-file-manifest.json) | Original repo-relative path, copied path, byte count and SHA-256 for each copied file |
| [benchmark-results.json](benchmark-results.json) | Lossless JSON-value extraction of all four HTML datasets, preserving metadata, warm-ups, measurements and empty scenarios |
| [measurement-summary.json](measurement-summary.json) | Derived per-metric samples, median, minimum, maximum and measured count; milliseconds; empty results are `null`, never zero |
| [source-locations.json](source-locations.json) | Repository roots/revisions, path prefixes, stable citation IDs and requested line ranges |
| [source-excerpts.json](source-excerpts.json) | Actual source text excerpts with line numbers, expanded paths, file SHA-256 and repository tracked status |
| [work-items.json](work-items.json) | Conceptual lane/work catalog W01–W26; all durations `null`; not an observed span graph |
| [collection-status.json](collection-status.json) | What was/was not collected, local HTTP checks, subject revision, limitations and external references |
| [user-telemetry-recipe.md](user-telemetry-recipe.md) | Preserved input recipe, distinct from source-verified instructions |
| [prepare_evidence.py](prepare_evidence.py) | Standard-library-only extraction/copying helper; never runs a sync |
| [traces/yahor/traces-1789726526259.json](traces/yahor/traces-1789726526259.json) | Byte-for-byte user-supplied Jaeger export, separate from the macOS benchmark datasets |
| [trace-manifest.json](trace-manifest.json) | Export source path, copied path, bytes and SHA-256 |
| [trace-analysis.json](trace-analysis.json) | Both traces, all normalized span rows and operation aggregates; native timestamps in microseconds, derived intervals in milliseconds |
| [analyze_trace.py](analyze_trace.py) | Reproducible Jaeger interval analysis and raw-copy helper |
| [test_evidence.py](test_evidence.py), [test_trace.py](test_trace.py) | Focused extraction and interval-accounting tests |

Datasets: `baseline`, `gradle-xxh3-hash`, `lookahead-deps`, `lookahead-deps-full`. There are **20 dataset/scenario records**: 18 with three measured samples plus one warm-up each, and two dependency-addition records without samples. That is **54 measured iterations and 18 warm-ups**; each successful iteration has three timing metrics.

## Reproduce the extraction

From the coroutines checkout root, Python 3.9+:

```sh
python3 import-overview/bin/prepare_evidence.py
python3 import-overview/bin/prepare_evidence.py --sources
python3 import-overview/bin/analyze_trace.py
python3 -B -m unittest discover -s import-overview/bin -p 'test_*.py' -v
```

The first command reads the four named original reports and current input files and overwrites only their named copies/derived JSON under this directory. It does not alter the originals, create a benchmark, or clear caches. The second additionally needs the two local source repositories at the paths in `source-locations.json`; it checks HEAD against the inspected revision before archiving working-tree excerpts. Full-file hashes and tracked status distinguish a working tree from a pristine commit. Rerunning after source/input changes can replace the evidence snapshot: preserve a copy/run ID first if retaining historical provenance matters.

Extraction uses `json.JSONDecoder.raw_decode` at the report's data declaration, validates units and finite nonnegative values, and retains raw metadata. Summary calculations use only `phase == "MEASURE"`. No normalization of scenario names or assumed timing-boundary conversion is performed.

Trace analysis checks span IDs/times, records parent-reference anomalies, clips immediate `CHILD_OF` intervals to each parent and calculates their union. `uncovered_by_direct_children_ms` means uninstrumented or uncovered elapsed coverage, **not CPU/self time**. Operation duration sums include overlap; `interval_union_ms` avoids double-counting time for that operation but still does not identify its critical-path contribution. Original tags, processes and references are retained; raw logs remain in the original export. Missing thread metadata stays null. Tests include overlapping/nested/disjoint/clipped intervals, missing/cross-trace parents, invalid inputs and empty data.

## Shape for a future interactive site

- **Observed samples:** join on `(dataset, scenario)`; use the original iteration ID/phase/number for identity. Never pair baseline/candidate iteration numbers as if they were synchronized experiments.
- **Work catalog:** join stable `W` IDs to lane ownership and citation IDs. Unknown durations remain `null`; don't spread coarse benchmark totals across stages.
- **Sources:** resolve citation ID → repository + expanded path + line ranges + excerpt/hash. Public-doc IDs and `local-build-inputs` live in `collection-status.json`.
- **Future traces:** keep the unmodified exporter format under `captures/<run-id>/`; derived span tables should explicitly name units, trace/span/parent IDs, process/service, attributes, status, original file and work-ID mapping confidence. Store epoch nanoseconds as decimal strings or big integers to avoid JavaScript number precision loss. Preserve Jaeger's native units rather than assuming every export is nanoseconds.
- **Manifests:** record software/binary hashes, cache-state dimensions, telemetry/parallel/phased/indexing flags, collector image, hardware/load, run outcome and timing boundaries. Do not overwrite a raw trace when deriving a normalized timeline.

No `captures` placeholder pretending to contain a new measurement is supplied; the supplied export is under `traces/yahor`. Create new run directories only for actual captures. Logs and source excerpts include machine paths and implementation details; review access rights, credentials and sensitive metadata before publishing them in a site or sharing outside the team.