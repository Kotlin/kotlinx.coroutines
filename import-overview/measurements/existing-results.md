# Existing measurements: what they establish

[Overview](../index.md) · [Capture a trace](../telemetry/collection.md) · [Raw evidence](../bin/README.md)

## Scope and provenance

These are **existing Gradle Profiler results**, not syncs run for this document. Original files came from `import-benchmarks/seb/{baseline,gradle-xxh3-hash,lookahead-deps,lookahead-deps-full}`. Byte-for-byte copies, SHA-256 hashes, extracted JSON and individual samples are in [bin](../bin/README.md). No elapsed times were inferred from source code.

All reports identify Gradle Profiler **0.25.2**, macOS **aarch64 26.6.2**, one warm-up and three measured iterations for each successful scenario. Definitions identify JBR `21.0.8-jbr` and Gradle heap `-Xmx3g`; logs show IDE heap `-Xms256m -Xmx4096m`. The original reports do **not** establish the IDE build, KGP source revision, hardware model, background load, or exact patch represented by each dataset name. Today's source revisions are not evidence of yesterday's installed binaries.

| Dataset label | Report date (UTC) | Reported Gradle version | Coverage |
| --- | --- | --- | --- |
| `baseline` | 2026-09-17 14:29:47 | `9.9.0-20260916220000+0000` | Eight successful scenarios; one failed |
| `gradle-xxh3-hash` | 2026-09-17 16:00:37 | `9.9.0-20260917154113+0000` | All-cold only |
| `lookahead-deps` | 2026-09-18 07:18:45 | `9.9.0-20260918071003+0000` | All-cold only |
| `lookahead-deps-full` | 2026-09-18 07:37:44 | `9.9.0-20260918071003+0000` | Eight successful scenarios; one failed |

The current wrapper points to a **local** `env/gradle/gradle-9.9.0-bin.zip`, not an internet download. Current build properties select `kotlin_version=2.5.255-SNAPSHOT`; both root/buildSrc repositories include `env/kotlin`. These current inputs are preserved under `bin/inputs`, but are **not historical run manifests**.

## Results

Times below are **seconds**, converted from raw milliseconds. Each median is calculated independently over the three `MEASURE` iterations; warm-ups are retained in raw JSON but excluded. Independent medians need not add up, even when each sample's components do.

Scenario names encode **Gradle User Home / Gradle daemon / IntelliJ caches**. They describe intent, not fully isolated controls: see the caveats below.

| Scenario (short form) | Baseline total median [min–max] | Baseline Gradle median | Baseline IDE median | Lookahead-full total median [min–max] |
| --- | ---: | ---: | ---: | ---: |
| Warm / warm / warm | 2.046 [1.965–2.459] | 1.104 | 0.942 | 1.957 [1.647–1.973] |
| Warm / warm / cold **¹** | 70.892 [68.265–73.716] | 11.538 | 60.084 | 42.268 [41.346–43.254] |
| Warm / cold / warm | 9.191 [7.438–10.179] | 8.880 | 0.311 | 6.472 [6.454–6.707] |
| Warm / cold / cold | 61.404 [61.177–62.048] | 10.802 | 50.602 | 37.883 [36.595–42.500] |
| Warm + root script change | 2.445 [2.187–2.919] | 1.490 | 0.955 | 2.618 [2.286–3.872] |
| Warm + buildSrc script change | 2.274 [2.230–2.636] | 1.334 | 0.981 | 4.650 [3.208–7.145] |
| Warm + core script change | 2.437 [2.304–2.749] | 1.515 | 0.964 | 5.369 [3.269–6.952] |
| Warm + dependency addition **²** | **No samples** | — | — | **No samples** |
| Cold / cold / cold | 154.418 [142.243–157.004] | 122.882 | 30.597 | 104.147 [100.505–104.655] |

All-cold comparison, retaining the two smaller datasets:

| Dataset | Total median [min–max] | Gradle median | IDE median |
| --- | ---: | ---: | ---: |
| `baseline` | 154.418 [142.243–157.004] | 122.882 | 30.597 |
| `gradle-xxh3-hash` | 124.029 [123.961–124.938] | 109.070 | 15.073 |
| `lookahead-deps` | 102.357 [100.238–102.749] | 86.599 | 15.340 |
| `lookahead-deps-full` | 104.147 [100.505–104.655] | 87.888 | 15.854 |

## Data-quality findings

1. **The “warm daemon / cold IntelliJ” scenario is confounded.** `performance.scenarios:44–52` says warm daemon, but baseline `profile.log:82–90` and lookahead-full `profile.log:76–84` describe `IDE with clean cache before build with cold daemon`. The latter log stops daemons again at `407–410`, before a measured iteration. Cold IDE scenarios also clear project `.gradle` caches and restart the IDE. Do not subtract these scenarios to claim a pure indexing, daemon, or IDE-cache cost.
2. **Dependency addition failed, not zero-cost.** Baseline `profile.log:1501–1516` and lookahead-full `profile.log:1495–1510` contain an `IdeGradleClient` → `GradleInvoker` `ClassCastException` during cleanup. Both HTML datasets have an empty iteration list for this scenario. The current scenario file contains a marker task; the current helper script does not implement the replacement described in its comment. Repair that harness before using this scenario.
3. **CSV is not safe as a rectangular table.** Commas in titles are unquoted, and failed-scenario sample columns are absent. In baseline, standard CSV parsing yields 94 columns in the title row, 28 in metric rows, and 26 in iteration rows. Preserve it, but extract the structured `const benchmarkResult` JSON from `benchmark.html` instead.
4. **No fine-grained timings here.** Logs say `Profiler: none` and `Build operations trace: false`. The three reported metrics are benchmark-defined timers, not a measured decomposition into the work items in the swimlane. In particular, “IDE execution time” is **not established as pure Workspace Model application or pure indexing**. Exact instrumentation boundaries need a Gradle Profiler source audit or an aligned trace.
5. **Preflight is not a measured sync.** Baseline `profile.log:15–61` performs an inspection build (`:help`), executes some buildSrc work, and stores a configuration-cache entry. Do not attribute its 39-second duration or task outcomes to a measured import.
6. **Different distributions and uncontrolled state.** Dataset labels suggest experiments, but source patches and randomized paired runs are absent. Baseline vs lookahead-full all-cold total medians differ by 50.271 s (32.6% lower); this is descriptive, **not proof of a hashing or dependency-lookahead speedup**. Warm build-script-change scenarios also get slower in that dataset.

## What to investigate first

- All-cold results justify breaking down **Gradle-side** work into startup, scripts/build logic, resolution/transforms, model building and transport.
- Cold-IDE scenarios justify measuring the **IDE-side** tail separately: conversion, model application, SDK/library setup, VFS scanning and indexing. First fix the scenario confounding.
- Warm no-change results are useful for detecting repeat model work, but three samples cannot establish a small optimization or a statistical confidence interval.
- A dependency-resolution optimization cannot be judged from the currently failed dependency-addition scenario.

For a controlled follow-up, pin IDE/KGP/Gradle binaries and hashes, record all cache dimensions, alternate baseline/candidate runs, preserve every sample and failure, and compare model equivalence as well as timings. See [investigation candidates](../analysis/duplication.md).