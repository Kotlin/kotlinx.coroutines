# Duplication and unnecessary-work investigation

[Overview](../index.md) · [Measurements](../measurements/existing-results.md) · [Capture](../telemetry/collection.md)

**Rule:** repeated API calls, files or span names are not sufficient proof of duplicated computation. Establish identical inputs, equivalent output requirements, repeated execution/cache misses and a removable dependency on the critical path. Preserve model correctness and incremental behavior.

## Prioritized candidates

| ID / priority | Evidence and trigger | What to measure | Safe decision criterion |
| --- | --- | --- | --- |
| **D1 / first correctness check**: repeat result processing | **Source-backed conditional path.** `ExternalSystemUtil.incompleteDependenciesState` runs the callback twice when its registry flag is false and the first run completes. The task state guard prevents another Gradle execution. [E01, E13](../reference/sources.md) | Count before-sync hooks, task execute attempts, Gradle actions, `importData`, success callbacks and after-sync hooks with the flag explicitly recorded | One invocation per intended refresh; retain failure/cancellation/incomplete-dependency semantics. Reproduce in a focused IDE test before proposing a fix |
| **D2 / high**: argument extraction more often or more fully than needed | **Version-dependent candidate.** Modern IDE service requests primitive/plugin arguments only; old compatibility code can resolve then discard a classpath and retry setup after failure. [K13–K14, B3](../reference/sources.md) | Per-task/API/contribution-set call counts; provider time; classpath/source enumeration; consumers of each result | Reuse only within a valid immutable scope; preserve user compiler/plugin options, classpath order, friend paths and unresolved-dependency behavior |
| **D3 / high**: overlapping dependency consumers | **Candidate.** Java/source-set models, Kotlin plugin arguments, script models and build logic have distinct consumers; Kotlin's conditional source-download branch can resolve Kotlin/Kotlinx groups again. [B1](../reference/sources.md) | Resolution/build-operation count by build/project/configuration/attributes; graph vs artifact vs download vs transform timings; cache outcomes | Share equivalent resolved results, not merely matching coordinates; preserve variant selection, substitution, scopes and source attachments |
| **D4 / high for cold runs**: repeated artifact reading/snapshotting | **Candidate, not proven duplicate hashing.** Gradle input tracking, Kotlin snapshot transforms, DSL classpaths and IDE indexes have distinct contracts. [K2, K6–K7](../reference/sources.md) | Bytes read/CPU per artifact, input normalization, snapshot granularity, transform cache hits, actual compiler task execution | Reuse only a representation meeting both contracts; validate ABI/non-ABI changes, classpath order, directories vs JARs and transitive changes |
| **D5 / medium**: unnecessary task/provider realization | **Source-backed opportunities.** Model inspection can demand task values; this build already has eager `getByName` calls | Realized vs executed task counts, stacks and first requester; same counts for plain configuration vs model action | Query enough for correct model without materializing unrelated tasks; preserve plugin callback effects. Do not blame model builders for build-script eagerness |
| **D6 / medium**: eager decoding of unused models | **Source-backed mechanism, unproven waste.** First IDE access decodes all stored models of that type. [E09](../reference/sources.md) | Requested/decoded/ultimately consumed model counts, encoded bytes, allocations and decode time | Lazy decode only wins if a meaningful subset stays unused and lookup/error semantics remain equivalent |
| **D7 / medium**: serialization bottleneck | **Source-backed mechanism, not duplication.** Single converter worker and phase-boundary future waits. [E08–E09](../reference/sources.md) | Build vs serialize overlap, queue delay, bytes, allocation, phase-send wait, peak retained memory | Reduce payload or improve overlap without classloader/thread-safety regressions; preserve streaming responsiveness and model identity |
| **D8 / medium**: repeated model-to-IDE traversals | **Candidate.** Separate hierarchy/source-set/dependency/task association passes; DataNode grouping and services; phased and legacy model paths coexist. [E06, E10, E12](../reference/sources.md) | Per-pass time/node count, changed vs unchanged entities, repeated root/library updates and notifications | Combine only compatible passes; verify imported entities, deletions/orphans, source sets, Kotlin settings and library order |
| **D9 / medium**: unnecessary acquisition on unchanged sync | **Candidate.** Connections can be reused, but resolver creates fresh action/model holders. [E04, E06](../reference/sources.md) | Model requests by identity across no-change syncs; which properties/environment/files invalidate results | A cache must include relevant build logic, Gradle/KGP/IDE versions, properties, environment and external dependency freshness; never cache solely on script timestamps |
| **D10 / measure separately**: IDE background tail | **Measured coarse bucket only.** Cold-IDE samples have large IDE-reported times, but reset multiple states. [Results](../measurements/existing-results.md) | Workspace changes, VFS refresh, scanning, library indexing, CPU and readiness boundaries | Avoid redundant notifications/roots; do not call indexing “unnecessary” merely because it follows sync; measure resulting editor correctness |

## Evidence added by the supplied Jaeger trace

The [38.660 s Linux import](../measurements/jaeger-trace.md) is a separate run from the macOS benchmarks. It strengthens **D3** as an investigation priority: 294 HTTP scopes cover 9.222 s, and 22 identical HEAD method/URL pairs repeat (23 extra occurrences). Distinct consumers or freshness checks can still justify them; no GET URL repeats. The dependency-model provider encloses 11.851 s, not an additional cost to add to the HTTP total.

For **D2/D5**, 21 JVM builder scopes total 1.343 s, with one taking 1.102 s, but project/argument-contribution tags are missing. For **D7**, 317 serialization scopes total only 0.460 s; this run does not support calling serialization the dominant bottleneck. For **D8**, result processing takes 2.719 s, while model commit's named scope is only 0.099 s. **D1 and D4 remain unconfirmed:** the main trace records one result-processing scope, and does not identify redundant IC fingerprint work. Overlapping progress roots in separate trace IDs do not prove two builds.

## Known mechanisms that already avoid some duplication

- Builder registration checks for an existing `ExtraModelBuilder`; repeated init hooks need not register new builders each time.
- Providers are grouped in ordered sets. Compatibility population methods are not automatically two equivalent requests.
- Phased IDE contributors claim phases once; synthesized callbacks and streamed callbacks are not evidence of duplicate updates.
- Converted IDE models are cached after type-wide decoding.
- Kotlin snapshot transforms are cacheable and registered once per project; registration counts are not execution counts.
- Downloaded artifacts can be shared even when distinct configurations or consumers resolve them.

## Minimum experimental design

1. **Repair the harness first:** get actual dependency-addition samples; separate IDE-cache reset from daemon reset and project-cache reset. Keep failed samples as failures.
2. Pin IDE build, enabled plugins, Gradle ZIP hash, KGP/artifact hashes, Java runtimes and all three source revisions. Installed snapshot version strings alone are insufficient.
3. Capture warm/no-change, script-only change, buildSrc change, dependency graph change, and controlled cold dimensions. Record offline mode, source/Javadoc policy, included builds, worker count and indexing policy.
4. Use unprofiled controls and identically instrumented candidate/baseline runs. Alternate order and retain all iterations; three existing samples only support descriptive summaries.
5. Join spans by trace/parent IDs and process identity; attach `(build, project, model, phase, task, configuration)` attributes where available. Add CPU/allocations/build operations for uninstrumented work.
6. Compare **outputs as well as speed**: modules, roots, source sets, dependency variants/scopes/order, outputs, language/API/JVM settings, plugin arguments, SDKs, tasks and unresolved-dependency diagnostics. Include a subsequent compilation after ABI and implementation-only changes when altering fingerprint reuse.
7. Report critical-path wall time, CPU time, bytes/allocations, cache hits and model-equivalence results separately. Do not add overlapping spans or subtract unlike cache scenarios to invent phase timings.

No candidate optimization was implemented, and no runtime speedup is established by this document. D1 is the strongest static duplicate-control-flow observation, but its false-flag condition is **nondefault** (declared default true, T18); the existing measurements cannot tell whether that branch was active.