# Work inventory by owner and demand

[Overview swimlane](../index.md) · [Machine-readable catalog](../bin/work-items.json) · [Sources](../reference/sources.md)

This is a checklist of work that **can** contribute to sync, not a claim that every row executes every time. `W` IDs are stable identifiers for a future interactive site. The catalog has no assigned per-row durations: measured spans from the [supplied trace](../measurements/jaeger-trace.md) cross these boundaries and overlap. Gradle internals summarized from public documentation are marked **general**; other references point to inspected source.

| ID | Owner / work | Inputs → outputs; when paid | Multiplicity / reuse | Evidence |
| --- | --- | --- | --- | --- |
| W01 | IDE: refresh orchestration | Saved documents, linked-project/settings state → sync task, before-sync hooks | Per requested refresh; already-running resolve guarded | E01–E03 |
| W02 | IDE / Tooling API: distribution and Java selection | Wrapper/local settings → installed Gradle, Java runtime, connection parameters | Acquire only if absent; cache/daemon compatibility matters | E03–E05; G3 (general) |
| W03 | Client / Gradle: daemon connect or boot | Compatible process or new JVM → initialized Gradle services | Per connection/build; boot only if reuse unavailable | E04–E05; G3 (general) |
| W04 | Client / Gradle: environment model | Tooling API `BuildEnvironment` query → version/environment checks | Before main model action; not a duplicate full project model | E05 |
| W05 | IDE → Gradle: tooling injection | Resolver extensions/classpaths/init scripts → registered model services | Per applicable build/classloader; registration checks existing builder | E06–E07 |
| W06 | Gradle: init/settings | Init/settings scripts, plugins, properties → build/project topology | Per participating build; compiled-script reuse conditional | G1–G2 (general); E07 |
| W07 | Gradle / repositories: build-logic classpaths | Plugin markers/buildscript dependencies → graphs, artifacts, classloaders | Multiple consumers; metadata/artifact caches; downloads only on demand | G2 (general); local root/buildSrc inputs |
| W08 | Gradle / compiler: buildSrc and required included-build outputs | Build logic + dependencies → reusable classes/plugins/JARs | Nested builds; executed/up-to-date/from-cache/no-source outcomes differ | K8–K12; G1–G2 (general); local buildSrc |
| W09 | Gradle: Kotlin DSL stages/accessors | Script text + classpaths + schema → executable scripts/accessors | Per script/stage; cache hits avoid compilation, not necessarily evaluation | G2 (general) |
| W10 | Gradle: project configuration | Script evaluation/plugin application/callbacks → source sets/tasks/configurations | Per project; can eagerly realize/resolve before model requests | K4–K6, K12; local build scripts |
| W11 | Gradle: provider scheduling/topology models | Root/nested builds + provider phases → targeted model requests | Ordered providers; conditional sequential/parallel project requests | E08, E14–E16 |
| W12 | Gradle: Java/source-set/task/dependency models | Configured project → tooling representations for modules, roots, outputs, tasks and dependencies | By model/project/source set; extensions add models | E06, E08; individual built-in builder internals not exhaustively audited |
| W13 | Gradle: Kotlin task-object access | Single-target compilations or task enumeration → applicable compile-task instances | All target compilations; fallback broad current-project enumeration | B1–B2 |
| W14 | Gradle: Kotlin compiler arguments | Task → selected argument contributions → serialized strings | Per surviving task; modern primitive + plugin classpath only; legacy path differs | B3–B4; K1–K3, K13–K14 |
| W15 | Gradle: Kotlin source-set metadata | Roots, flags, visible/generated source sets → Kotlin model fields | Per task/source set/project; directory reads do not run generators | B1, B5–B7 |
| W16 | Gradle / repositories: dependency and source acquisition | Demanded configurations/variants → resolved graph and artifact paths | Can occur in W07/W10/W12/W14; conditional Kotlin/Kotlinx sources branch; cache hits vs actual I/O | B1; K2; E03; general resolution distinction |
| W17 | Gradle / disk: fingerprints and transforms | Declared inputs/artifacts → cache keys or transformed outputs | Demand/cache/attribute dependent; no proof of mandatory application IC snapshots during sync | K2, K6–K9; Gradle implementation not audited |
| W18 | Gradle conversion worker: model encoding | Built model object → selected encoding/bytes or fallback object | Single conversion executor; overlaps producers, waits at phase drains | E08d–E08e, E09a–E09c |
| W19 | Tooling API → IDE: state transfer and event queue | Phased/streamed/final state → stored IDE model payloads and notifications | By phase/batch; transport size and queue delays need measurement | E08a–E08c, E10a–E10b |
| W20 | IDE: decode tooling models | Stored payloads → classloader-appropriate objects | First access decodes stored models of a type; replacements cached | E09d |
| W21 | IDE: phased model application | Available phase models → contributor models/Workspace Model changes | Conditional phased path; at-most-once phase claims | E10c |
| W22 | IDE: resolver/DataNode conversion | Build hierarchy + models → project/module/source-set/library/task/Kotlin nodes | Multiple association passes; argument parsing/normalization/interning | E06, E11 |
| W23 | IDE: data services and commit | Grouped/ordered DataNodes → modules, roots, libraries, SDK/settings and entity changes | Import lock; services; orphan removal; bridge/Workspace Model commit | E12 |
| W24 | IDE: post-import and completion | Applied/partial results → callbacks, hooks, notifications, possible VFS refresh | Per result handling; D1 identifies a conditional repeat path | E01–E02, E12–E13 |
| W25 | IDE background: VFS/scanning/indexing | Changed roots/files/libraries → index/editor readiness | Can overlap sync; conditional pause; completion is a separate boundary | E01–E02; deeper indexing implementation not audited |
| W26 | IDE + daemon: telemetry overhead | Context/spans → buffers, serialization and collector I/O | Only enabled paths; two exporters, separate from model transport | Telemetry references T01–T18 |

## Cross-cutting work not represented as a separate sequential phase

- Filesystem metadata, directory traversal, cache locking, artifact transforms, repository authentication/retries, classloading, JIT, GC and allocation can occur inside many rows. Attribute them using operations and CPU/allocation profiles; do not invent a standalone “hashing phase.”
- Compilation toolchain detection/provisioning, source/Javadoc attachment policy, Kotlin DSL editor models, generated-source preparation, before/after-sync tasks and third-party plugins add conditional branches. This inventory does not prove that this project runs all of them.
- Gradle buildSrc discovery has an older-than-8.0 compatibility branch in the inspected resolver. Do not add its cost unconditionally to modern Gradle results.
- Failure, retry, cancellation, unavailable optional models and partial data application are paths in the pipeline, not missing zero-duration stages.

## Timing boundaries

`GradleConnection` contains its supplied operation, not just handshake. `GradleCall` includes event collection and can overlap IDE contributors. A delay before Gradle's `Run build` may include more than daemon startup. `WorkspaceModelApply` is the commit span, not all IDE work. Use the [span guide](../telemetry/span-reference.md) before mapping traces to these rows.