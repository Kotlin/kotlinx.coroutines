# Kotlin/JVM: model inputs, arguments and fingerprints

[Overview](../index.md) · [IDE pipeline](intellij.md) · [Source map](../reference/sources.md)

## Three operations that must not be conflated

1. **Configure** a Kotlin compilation/task and wire its providers/configurations.
2. **Inspect** it for an IDE model, potentially evaluating providers and resolving files.
3. **Execute** its task action and compile sources.

The first two can happen during a normal sync without the third. BuildSrc or plugin-producing included builds are the important exception: their output may be needed to configure the imported build, so their compilation tasks can execute. Arbitrary plugins or explicitly requested sync tasks can introduce other execution.

The inspected KGP source and IntelliJ-injected builder join at `IdeCompilerArgumentsResolver`. They establish the ordinary JVM path below; do not assume every model request exercises every KGP API.

## Actual model-builder path

The injected `KotlinGradleModelBuilder` is registered as a `ModelBuilderService`. Its `AndroidAwareGradleModelProvider` inherits **`ADDITIONAL_MODEL_PHASE`** and delegates requests to `GradleModelProviderUtil`. The utility's controller defaults to project-level requests over `buildModel.projects` for the supplied builds. Depending on `isParallelModelFetchEnabled()`, it loops sequentially or submits target actions with `BuildController.run`; this is a real conditional parallel branch, not simultaneous execution of all provider phases ([B1, B8, E14–E16](../reference/sources.md)).

For each project invocation, the builder checks applicability, obtains task objects, gathers arguments/metadata and returns `KotlinGradleModel`:

- A recognized single target leads to enumeration of **all its compilations**, reflected compile-task names, and `project.tasks.findByName`. The fallback uses `project.getAllTasks(false)[project]` and a task-class whitelist. These are eager object lookups, **not** `TaskProvider.get()` in this builder. Recognized targets with zero compilations do not take the fallback.
- Source-set filtering occurs after task lookup. Each surviving task requests compiler arguments, interns strings within this builder invocation, and stores arguments keyed by source-set name. Two tasks with the same key would overwrite the stored entry without avoiding earlier extraction.
- Additional visible source sets, Kotlin-only roots/task flags and generated-source roots are collected. Reading directories is not running their generation tasks. The generated-root branch is version-gated for KGP 2.3+.
- A **separate source-download branch** can resolve `org.jetbrains.kotlin` and `org.jetbrains.kotlinx` sources when a builder context exists, the general policy does not already download sources, and `idea.gradle.download.sources.force` is absent. For Gradle 7.3+, it visits Java source sets whose compile classpath is a resolvable configuration; older Gradle builds a detached configuration from matching declared dependencies. The broad group filter is not limited to stdlib. A resolve call does not prove a download/cache miss.

These branches are in [B1–B8](../reference/sources.md). Android parameter handling and the IDE's MPP branch differ; this is not a universal Android/MPP model description. In particular, do not interpret the builder's `"*"` parameter as a general-purpose wildcard: its Android early-skip and literal source-set filtering have different behavior.

## Compiler arguments are a demand boundary

`KotlinCompilerArgumentsProducer` separates contributions into four categories ([K1](../reference/sources.md)). For JVM tasks, `KotlinCompile.createCompilerArguments` implements them ([K2](../reference/sources.md)):

| Contribution | Work visible in KGP source | Possible cost when requested |
| --- | --- | --- |
| `Primitive` | Read compiler options and compiler-plugin option providers | Provider evaluation and bean/string construction; plugin option providers can have their own work |
| `PluginClasspath` | Combine file collections and call `toPathsArray()` | Resolve compiler-plugin artifacts and materialize file paths |
| `DependencyClasspath` | Read friend paths and `libraries.toList().filter { it.exists() }` | Resolve/materialize library files; filesystem existence checks |
| `Sources` | Enumerate Kotlin, Java and script sources | Source-tree/file-collection traversal |

The producer's default selects all categories, but **the modern IDE caller restricts them**. IntelliJ loads `IdeCompilerArgumentsResolver` through the task classloader and calls `instance(project).resolveCompilerArguments(task)` ([B3–B4](../reference/sources.md)). In this KGP revision, `IdeCompilerArgumentsResolverImpl` requests **only `Primitive` and `PluginClasspath`, with `isLenient=true`** ([K13–K14](../reference/sources.md)). Its comment says the plugin classpath is retained for IDE plugins such as serialization support. It does **not** request `DependencyClasspath` or `Sources` here. Plugin-option providers and the separate source-download branch can still do work. Lenient mode catches failures; it does not make attempted resolution free.

When that service is unavailable, the old non-Native compatibility path calls `createCompilerArgs` and `setupCompilerArgs`, retries setup with ignored classpath issues on failure, and then clears the classpath before serialization. Its comment explicitly says older KGP can resolve the classpath before discarding it ([B3](../reference/sources.md)). That is a concrete legacy unnecessary-work candidate; do not project it onto the modern service. A present modern service returning null does not trigger this fallback.

Compatibility matters: `CompilerArgumentAware` is documented for IDEs before 2023.2 ([K3](../reference/sources.md)). Its “full” legacy serialization requests primitive + plugin-classpath contributions, while its default-arguments path requests primitives only. Neither requests the dependency/source contribution in this inspected implementation. The method name “serialized compiler arguments” alone therefore does not establish compile-classpath resolution.

Compiler argument extraction is not a compiler invocation. The actual `@TaskAction` and `callCompilerAsync` path are separate ([K8–K9](../reference/sources.md)).

## Compiler plugins and task realization

`SubpluginEnvironment` finds applied `KotlinCompilerPluginSupportPlugin`s, declares their compiler artifacts, obtains options, and configures compile-task providers. `AbstractKotlinCompileConfig` attaches their configuration with `pluginClasspath.from(...)` ([K4–K5](../reference/sources.md)). This wires deferred work; it is not a download at registration time.

One concrete realization boundary is `project.provider { taskProvider.get().libraries }` in `KotlinCompileConfig` ([K6](../reference/sources.md)). Evaluating that provider obtains the task. It does not prove that all tasks are realized during sync, nor that the import's builder evaluates this particular provider. Conversely, the imported build's own eager `getByName` calls can realize tasks before the builder ([examples](gradle-preparation.md)).

## “Fingerprint dependencies” is several different contracts

| Layer | Purpose and source evidence | Sync interpretation |
| --- | --- | --- |
| Gradle input tracking/cache keys | KGP declares `@Classpath` inputs on tasks/transforms; Gradle implements their tracking | Work depends on demand, cache state and normalization; exact Gradle internals not audited here |
| Kotlin classpath snapshot transform | `@CacheableTransform` consumes JAR/directory artifacts, runs JVM snapshotting and saves `-snapshot.bin` | Registering the transform does not execute it; requesting its output may |
| Kotlin IC change analysis | `getClasspathChanges` consumes snapshot files, prior shrunk snapshot and Gradle `InputChanges` | In the compiler invocation path; not established as mandatory model work |
| Kotlin DSL/script classpath processing | Enables compiled-script reuse and script compilation | A different consumer from application Kotlin IC; do not merge their timers |
| IDE indexes | Enable navigation/analysis over source and libraries | Separate IDE work, not a Gradle input fingerprint |

Specific KGP observations ([K2, K6, K7](../reference/sources.md)):

- Raw `KotlinCompile.libraries` is `@Internal`; the comment says snapshot inputs replace it for compile avoidance. The transformed snapshot collection is `@Classpath` / `@Incremental`.
- Transform registration is guarded once per project, and covers both JAR and directory artifacts.
- The transform's input artifact **and** build-tools classpath are `@Classpath`. The transform itself performs actual Kotlin snapshot generation on a cache miss.
- Snapshot granularity can differ: class-level for Gradle-user-home/read-only-cache artifacts and `android.jar`, class-member-level otherwise. “Same JAR bytes” alone is not a sufficient reuse key.
- Reading raw libraries for arguments does not itself establish a request for `classpath-entry-snapshot` artifacts.

Thus the draft's two fingerprint bullets should be two **potential consumers**, not an assertion that every dependency is unconditionally hashed twice during every sync. To prove duplication, collect artifact identity/content, requested attributes, normalization/granularity, consumers, cache hits and actual read/CPU counts.

## Compilation and process boundaries

The inspected `GradleCompilerRunnerWithWorkers` submits via `workerExecutor.noIsolation()`; that worker is **not itself another JVM**. Its compiler-work path can connect to a Kotlin daemon for the `DAEMON` strategy or compile in-process, including configured fallback ([K10–K11](../reference/sources.md)). Other runner/version paths may differ.

The compilation task validates its compiler classpath (which may trigger resolution), prepares inputs/outputs and IC state, and invokes the compiler. Its complete process lifetime is not a task duration: startup, classloading, idle periods and multiple compilations may share a JVM.

## Investigation hooks

- Count argument requests by `(build, project, task, API, contribution set, model phase)`. Fresh beans/repeated provider evaluation are plausible; repeated downloads are unproven.
- Distinguish `buildscript`, `pluginClasspath`, `libraries`, `kotlinCompilerClasspath` and `kotlinBuildToolsApiClasspath`. Same coordinates in two classpaths do not imply the same purpose or cache contract.
- Record actual snapshot-transform executions and outputs before claiming IC work during sync.
- Preserve unresolved dependencies/import errors when testing shortcuts; lenient import is a feature, not evidence that failed work was never attempted.