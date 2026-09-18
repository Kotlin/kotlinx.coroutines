# Kotlin/JVM Gradle import: work and swimlanes

**Purpose:** identify where IntelliJ sync spends work, which work can be reused, and which apparently repeated operations need investigation. Prepared 2026-09-18 from the supplied Kotlin/IntelliJ checkouts, existing kotlinx.coroutines benchmarks, and the supplied Yahor Jaeger export.

**Reading key:** **source-backed** means the inspected implementation has this path, not that every sync executes it; **measured** means an existing sample exists; **candidate** means an optimization hypothesis, not proven waste. No new sync, cache clearing, IDE restart, or telemetry service was started for this document.

## Start here

| Question | Detail |
| --- | --- |
| What runs where, and in what order? | Swimlane below; [work inventory](pipeline/work-inventory.md) |
| What precedes model building? | [Bootstrap, build logic and configuration](pipeline/gradle-preparation.md) |
| What does Kotlin add? | [Kotlin/JVM models and compiler arguments](pipeline/kotlin-models.md) |
| How do models reach the IDE project? | [IntelliJ model acquisition and application](pipeline/intellij.md) |
| What might be duplicated? | [Investigation candidates and validation criteria](analysis/duplication.md) |
| What has actually been measured? | [Existing results and data-quality findings](measurements/existing-results.md) |
| What happened in the supplied trace? | [Measured timeline and trace findings](measurements/jaeger-trace.md) |
| How do we capture a real timeline? | [OpenTelemetry and profiling recipe](telemetry/collection.md) |
| Where is the evidence? | [Source map](reference/sources.md); [raw data and schemas](bin/README.md) |

## Swimlane: a logical timeline, not a duration chart

Each participant is an ownership lane. The Tooling API client may run in the IDE process or an external-system helper process, depending on the launch mode. Builders injected by IntelliJ **execute in Gradle**, not in the IDE. Compiler/worker processes are conditional. Arrows show prerequisites and data flow; a trace is needed for actual parallelism and elapsed time.

```mermaid
sequenceDiagram
    participant IDE as IntelliJ orchestration
    participant TAPI as Tooling API client / helper
    participant G as Gradle daemon + model builders
    participant C as Compiler / worker JVMs (optional)
    participant IO as Repositories + disk caches
    participant M as IntelliJ model / background work

    IDE->>IDE: Refresh request, settings, JDK, extensions
    IDE->>TAPI: Prepare connection, injected init scripts, model providers
    opt Distribution not installed
        TAPI->>IO: Download or read local Gradle ZIP, unpack and validate
    end
    TAPI->>G: Connect to compatible daemon or start one
    TAPI->>G: Build action, model requests and trace context
    G->>G: Init scripts; settings; included-build discovery
    opt Early projects-loaded results
        G-->>TAPI: Early model state
        TAPI-->>IDE: Phase notification and available models
        IDE->>M: Applicable early project-model updates
    end
    G->>IO: Resolve build-logic plugins and classpaths
    opt Build logic needs compilation
        G->>C: buildSrc / required included-build tasks
        C->>IO: Compiler inputs, snapshots, outputs and cache entries
        C-->>G: Build-logic classes / JARs
    end
    G->>G: Compile or reuse staged Kotlin DSL scripts; apply plugins; evaluate projects
    Note over G,IO: Resolution and compilation interleave with configuration; not one global pass
    loop Applicable model phases / builds / projects
        G->>G: Model providers invoke builders; realize queried tasks/providers
        G->>IO: Resolve requested dependencies, artifacts, transforms, toolchains
        G->>G: Java/source-set + Kotlin models; compiler argument beans
        G-->>TAPI: Serialized model payloads / phased results
        TAPI-->>IDE: Deserialize and dispatch available models
        IDE->>IDE: Resolver extensions build / enrich DataNodes
    end
    IDE->>M: Import data services; merge modules, roots, libraries, Kotlin settings
    M->>M: Commit project-model changes, callbacks and follow-up activities
    Note over IDE,M: Streaming can overlap Gradle work; completion is not indexing completion
    M->>M: VFS refresh / scanning / indexing as scheduled (may overlap sync)
```

Plain-text equivalent: **IDE refresh → connection/distribution/daemon → Gradle initialization and build-logic preparation ↔ project configuration → phased model construction ↔ model transfer and IDE conversion → project-model application → post-sync work**. Early projects-loaded results can precede complete project configuration. Repository I/O and cached-file reads can occur at several points; build-logic compilation can introduce nested builds and extra JVMs.

## Corrections to the initial draft

- Download a **Gradle distribution**, not a daemon. Reuse an installed distribution and a compatible running daemon where possible. Downloading a Gradle JDK/toolchain is another conditional operation.
- “Build init” is not a bucket containing all script compilation. Settings/init/project scripts have different stages; script classpaths, generated accessors, buildSrc and plugins create prerequisites. Compilation and evaluation are interleaved and cached.
- `buildSrc` and necessary included-build **build logic** can execute compilation tasks during sync. This does **not** mean normal application `compileKotlin`, tests or packaging run merely because their tasks are inspected.
- Plugin application is part of script evaluation, rather than a completely separate pass. User build logic can eagerly realize tasks or resolve configurations before any model builder runs.
- Dependency **declaration**, graph **resolution**, artifact **download**, artifact **transform**, and classpath **fingerprinting** are different work. A resolution call is not proof of another download.
- Gradle fingerprints and Kotlin incremental-compilation snapshots serve different contracts. Repeated reads of the same JAR are worth investigating, but are not automatically redundant hashing.
- IntelliJ selects/injects tooling support **before** builders are used. Phased model building, serialization, IDE deserialization and conversion may overlap; not every model travels through one universal Java-serialization path.
- Project resolvers usually consume the model to produce/enrich `DataNode`s; data services then apply them. Workspace Model updates, VFS work and indexing are separate boundaries, not synonyms for “import finished.”

## Findings worth acting on

1. **Measure before removing work.** The source map reveals repeated-query opportunities, but does not prove duplicate downloads, snapshots or model construction in a particular run.
2. **Existing all-cold samples are expensive:** baseline median 154.418 s total, versus 2.046 s for warm/no-change sync. These are benchmark-defined totals, not individual swimlane timings.
3. **Fix measurement controls first:** the dependency-addition scenario has no samples after a cleanup exception; a “warm daemon / cold IDE” scenario actually stops daemons. The structured HTML data is usable; the CSV is not a rectangular table.
4. **Separate the IDE tail:** cold-IDE benchmark buckets are large, but do not identify conversion, model application, scanning or indexing individually. Collect aligned spans and CPU profiles before attributing them.
5. **The supplied trace narrows the priorities:** a 38.660 s Linux sync contains an 11.851 s dependency-model provider scope and 9.222 s of recorded HTTP requests, with 22 repeated HEAD method/URL pairs. Serialization totals only 0.460 s. These scopes overlap; see the [measured timeline](measurements/jaeger-trace.md), not an additive cost estimate.
6. **Telemetry key correction:** this source revision checks `gradle.daemon.opentelemetry.agent.enabled`, not the historical key without `.agent`. The [recipe](telemetry/collection.md) documents version checks and export/flush caveats.

The overview is Kotlin/JVM-focused. Android, multiplatform, native, JavaScript, project-specific plugins, Gradle/IDE version differences and feature flags introduce additional branches. The inspected coroutines checkout currently applies the JVM plugin; it is not a representative trace of every Kotlin build.