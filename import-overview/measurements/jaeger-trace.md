# Supplied Jaeger trace: measured import timeline

[Overview](../index.md) · [Benchmark results](existing-results.md) · [Raw export](../bin/traces/yahor/traces-1789726526259.json) · [Derived span data](../bin/trace-analysis.json)

## Provenance and coverage

The user supplied `import-benchmarks/yahor/traces-1789726526259.json`: **17,156,527 bytes**, SHA-256 `7b20f18661f9f024ad566813dda4b6607f37013db4dad58e8827e0a0c7ef224c`. The copy and [manifest](../bin/trace-manifest.json) preserve it unchanged. No new import was run for this analysis.

| Trace | Canonical spans | UTC interval on 2026-09-17 | Envelope |
| --- | ---: | --- | ---: |
| `dcfcfc0dad45c9d6133a42c9202d8dae` (**B**, main analysis) | 969 | 08:48:06.784000–08:48:45.444204 | **38.660204 s** |
| `06fadc3b5d914d58348098e52c246ea6` (**A**, progress-only) | 2 | 08:48:07.084080–08:48:45.447144 | 38.363064 s |

Both roots are named `Progress: Importing 'kotlinx.coroutines' Gradle Project`. A contains only a root (`0cad5ca45d914d58`) and a 0.033 ms “completing” span; B's root is `0f6696164690c06f`. They overlap but have **no cross-trace parent references**. Do not add their durations or infer two Gradle builds. Across both traces there are **971 canonical spans**; ancestor objects embedded in `references[].span` are copies, not additional events.

Every recorded parent reference resolves; no recorded child interval lies outside its parent. Both trace warnings are null, with no span warnings or log events. There is no explicit root success status or export-level errors field. B has 14 error-tagged spans, all HTTP 404s; these do **not** establish that the overall import failed. Structural integrity does not prove instrumentation completeness or correct causality for every recorded edge.

## This is a different environment from the benchmark reports

| Process / field | Captured value |
| --- | --- |
| B / `p1`, 758 spans | Service `unknown_service:java`; command line explicitly launches `org.gradle.launcher.daemon.bootstrap.GradleDaemon` |
| B / `p2`, 211 spans; A / `p1`, 2 spans | Service `IntelliJ IDEA`, version **262.10968.63**, namespace `IU`; matching IDE service-instance ID |
| Gradle | **9.6.1**, present in daemon command arguments/distribution paths |
| Daemon Java / heap | OpenJDK Runtime Environment **21.0.12+8**, Gentoo VM; `-Xmx3g` |
| Host | Linux **7.2.4-gentoo-yahor**, amd64; `yahor-note` |
| Instrumentation | Java agent distribution **2.8.0**, OTel SDK **1.42.1** |
| Unknown | Applied KGP version, source revisions, cache warmth/hits, daemon reuse history, benchmark iteration and intended readiness boundary |

Requested Kotlin artifact URLs mention **2.3.21**, but are not sufficient proof of the applied KGP version. Do not map the local snapshot properties or macOS benchmark scenario names onto this run. The trace uses `GetBuildEnvironment` whereas the inspected source uses `GetModel`; runtime/source differences are real, so source names are guides rather than guaranteed exact matches.

## Measured swimlane overview

All following offsets are seconds from B's root. Windows are rounded for readability and are **not disjoint costs to add**. Exact span offsets/durations are in the JSON.

| Owner | 0–14.7 s | 14.7–16.7 s | 16.7–28.6 s | 28.6–30.7 s | 30.7–35.3 s | 35.3–38.7 s |
| --- | --- | --- | --- | --- | --- | --- |
| IDE orchestration | Initial phase, environment query, `GradleCall` wait/processing | `GradleCall` continues | Continues | Continues | Receives last phase; call ends at 35.291 | Resolver conversion, result import, completion |
| Gradle model-action scopes | First action, root/nested build and daemon-classloader acquisition | Project and source-set phases | Dependency-model phase | Script-model phase | Additional-model phase ends 34.890 | No claim of further daemon work from this export |
| IDE phased contributors | Base-script phase around 7.014 | Project phase 14.760 | Source-set phase 16.715 | — | Script phase 30.678; additional phase 35.252 | Legacy data services follow |
| Converter worker | Model encodings interleave with production; **317 spans / 0.460 s total over the run**, not one contiguous block | ↔ | ↔ | ↔ | ↔ | — |
| Repository I/O | Recorded requests occur within model-related scopes; **294 requests / 9.222 s union over the run**, not an additional phase | ↔ | ↔ | ↔ | ↔ | — |
| IDE project model | Early contributor updates where enabled | ↔ | ↔ | — | ↔ | Data services 35.924–38.603; `WorkspaceModelApply` at 37.727 |

The IDE spans have no thread tags; their thread is **unknown**, not necessarily the UI thread. Daemon spans identify `Daemon worker` (thread 73, 441 spans) and `idea-tooling-model-converter` (thread 126, 317 spans). Nested/overlapping scopes do not measure the number of concurrently executing threads.

## Selected spans: exact measured durations

Milliseconds below. “Uncovered” is duration minus the **union of immediate `CHILD_OF` intervals clipped to that span**, not exclusive CPU time. Several logically enclosing daemon scopes are recorded as siblings under `GradleCall`, so a full-duration uncovered value on those wrappers does not mean no other instrumentation covers that time.

| Span ID | Operation | Start offset (ms) | Duration (ms) | Uncovered (ms) |
| --- | --- | ---: | ---: | ---: |
| `ae56f846ede5e5c1` | `ExternalSystemSyncProjectTask` | 10.712 | 38649.228 | 408.010 |
| `e98c47bfa1d6492f` | `GradleConnection` | 434.019 | 35386.889 | 99.655 |
| `f82c10bd48ec1eb0` | `GetBuildEnvironment` | 500.721 | 588.254 | 588.254 |
| `53ae121ffc8e9f85` | `GradleCall` | 1121.780 | 34168.721 | **6139.834** |
| `a2309d1cdab379c5` | `InitAction` | 7004.406 | 7632.368 | 7632.368 |
| `9cb5bfd663c73c96` | `GetMainGradleBuild` | 7004.748 | 3418.976 | 3418.976 |
| `605f20a8d9fc3c20` | `GetDaemonClassLoader` | 10426.282 | 4189.603 | 4189.603 |
| `f84860885d97b666` | `GradleSourceSetModelProvider` | 14759.456 | 1941.699 | 1711.906 |
| `80be751734c53a9c` | `GradleSourceSetDependencyModelProvider` | 16714.540 | **11850.719** | 4952.387 |
| `43eea92fa236814e` | `KotlinDslScriptsModel` | 28586.236 | 1761.538 | 711.581 |
| `4d2709cfd529b688` | `GradleBuildScriptClasspathModelProvider` | 30347.891 | 327.785 | 56.394 |
| `cd230ce426de3102` | `AndroidAwareGradleModelProvider` | 30681.959 | 1356.735 | 1356.735 |
| `5d009850018773f3` | `GradleProjectResolverDataProcessing` | 35290.585 | 530.259 | 388.295 |
| `7e1212343d247c16` | `ExternalSystemSyncResultProcessing` | 35907.855 | 2718.906 | 40.257 |
| `da0503a405fb5014` | `ProjectDataServices` | 35923.951 | 2678.649 | **963.061** |
| `67df0be37193c8ed` | `postImportTasks` | 37126.447 | 563.187 | 563.187 |
| `85683e087519a874` | `WorkspaceModelApply` | 37726.641 | 99.491 | 98.399 |
| `9b2f5bd1068f67b3` | `runFinalTasks` | 37839.263 | 763.316 | 763.316 |

The 6.140 s uncovered inside `GradleCall` is a **measurement gap/investigation target**, not established IDE overhead, daemon startup, CPU work or removable waste. Likewise, `GetDaemonClassLoader` is an acquisition scope, not proof that 4.190 s was spent purely loading classes. Add lower-level operations/profiles before assigning causes.

## Repetition: observed versus inferred

| Captured operation | Count | Sum of durations | Interpretation |
| --- | ---: | ---: | --- |
| `SerializeGradleModel` | 317 | **459.957 ms** | Interval union also 459.957 ms, about 1.19% of B's envelope; **not evidence of a dominant serialization bottleneck** |
| `kotlin_import_daemon_jvm_param_buildAll` | 21 | **1343.103 ms** | Builder scope, not isolated argument extraction; project/model/phase tags absent |
| `kotlin_import_jvm_createModule` | 21 | 33.46 ms (rounded) | IDE-side module path; repeated modules are expected, not proven duplicates |
| `kotlin_import_daemon_kapt_buildAll` | 21 | 0.700 ms | Tiny eligibility/model work can be legitimate even without substantive output |
| `kotlin_import_daemon_mpp_buildAll` | 21 | 2.932 ms | Invocation does not prove the project is multiplatform |
| `kotlin_import_daemon_prepare_kotlin_ide_import_buildAll` | 21 | 2.520 ms | Do not infer 21 compiler invocations |

The slowest JVM builder scope is `d5f4c8f67cc7fa8f`: **1101.875 ms**, starting at 30684.856 ms. The next is `e2a35a6e4d1321d4`: **107.880 ms**. Attribution to a project, compiler-argument contribution, classloading, or source downloading needs more tags/stacks. Serialization `model.class` values include proxy classes; matching proxy types do not identify the same model instance.

Two `ProjectImportAction` scopes and two `ExecuteAction` scopes appear, consistent with a phased-action architecture. The long action and execute scopes almost coincide and both reference `GradleCall`; they are not two sequential 20-second costs. Seven `SendPendingState` spans carry `use-streamed-values=true`. There is only one captured `ExternalSystemSyncResultProcessing` and one `WorkspaceModelApply` in B: this export does **not** demonstrate source candidate D1's duplicate-result path.

## Repository work is the strongest concrete repetition lead

| HTTP method | Count | Duration sum and interval union | 200 / 404 |
| --- | ---: | ---: | ---: |
| GET | 161 | 4938.441 ms | 156 / 5 |
| HEAD | 133 | 4283.284 ms | 124 / 9 |
| Combined | **294** | **9221.725 ms** | **280 / 14** |

The recorded HTTP spans do not overlap one another. This does not establish all network activity, bytes downloaded, cache misses, or 9.222 s of removable critical-path work. HEAD checks and GET retrievals serve different purposes.

- **186 distinct URLs**; 96 recur when ignoring method. More precisely, **22 identical `(method, URL)` pairs repeat**, yielding **23 occurrences beyond the first**. All are HEAD; no identical GET URL repeats.
- One source URL receives three HEAD requests: `https://repo.maven.apache.org/maven2/org/jetbrains/intellij/deps/coverage-report/1.0.25/coverage-report-1.0.25-sources.jar`.
- Fourteen 404s occur across **Google Maven (7), Maven Central (3), Gradle Plugin Portal (3), and JetBrains Dokka development repository (1)**. They include missing sources and plugin-marker sources, and Kotlin artifact POM probes against repositories that may not host them.
- Examples: the Dokka repository's HEAD for `org.jetbrains.kotlin:kotlin-reflect:2.3.21` takes **417.942 ms** (`43a9f7aa7d253795`); Google Maven's GET for `kotlin-stdlib-common:2.3.21` takes **193.241 ms** (`8e123bc28946ddea`). All request URLs/statuses and repeated method/URL groups are retained in `trace-analysis.json`.

Investigate repository content filters/order, negative-result caching, repeated source-attachment requests, and whether distinct model consumers re-check the same artifact. Preserve repository substitution/content semantics and source navigation. A repeated HEAD can be necessary freshness checking; do not delete it solely because the URL repeats.

## What this trace changes in the investigation plan

1. Prioritize dependency-model work and its repository requests (D3), then the expensive first Kotlin builder invocation and setup/acquisition scopes. Keep compiler-argument extraction separate from the enclosing builder.
2. Instrument the 6.140 s `GradleCall` coverage gap and the 0.963 s uncovered in `ProjectDataServices` before classifying them as unnecessary work.
3. Retain script editor/model work (`KotlinDslScriptsModel`) and later IDE import tasks in the overview: sync is not just compilation-task inspection.
4. Deprioritize broad serialization tuning for this particular run unless allocation/queue evidence suggests a hidden issue; hundreds of tiny spans are not automatically expensive.
5. Do not claim duplicate Kotlin IC hashing, duplicate downloads, double sync execution, indexing completion or a speedup. Those conclusions require additional evidence beyond this single supplied trace.