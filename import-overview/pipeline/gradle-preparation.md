# Before models: bootstrap, build logic and configuration

[Overview](../index.md) · [Work inventory](work-inventory.md) · [Source map](../reference/sources.md)

## 1. IDE preparation and connection

The IDE resolves linked-project settings, Gradle distribution selection, Gradle JVM, offline mode, arguments, resolver extensions and tooling support. It prepares init scripts that make IntelliJ's model builders available in the Gradle process. Connection setup can involve an external-system helper; this is not the Gradle daemon itself.

Conditional costs:

- Locate/download/unpack/validate the **Gradle distribution** selected by wrapper, installation or IDE settings. A warm distribution cache eliminates acquisition, not connection work.
- Locate an appropriate Java runtime; depending on settings/version, daemon-JVM provisioning or compilation toolchain resolution can incur additional I/O. Keep these distinct from downloading Gradle.
- Discover/connect to a **compatible** daemon, or launch a JVM and initialize Gradle. Compatibility depends on more than the version: Java home and JVM requirements matter. Warm filesystem caches do not imply warm classes/JIT.
- Acquire cache/file locks, initialize services, load classes and build scripts, and establish cancellation/progress/telemetry plumbing. Idle/wait time belongs on the wall-time timeline, but is not CPU cost.

Gradle's public lifecycle and daemon documentation support the general distinctions ([G1–G3](../reference/sources.md)). Exact bootstrap internals of the custom 9.9 distribution were not audited.

## 2. Initialization is not all preparation

Gradle's formal initialization phase establishes settings, projects and included builds. Init scripts and settings plugins can contribute work before project configuration. Settings Kotlin DSL scripts themselves need classpaths and compiled code.

The draft's “build init” work actually spans several lifecycle locations:

| Work | Why it happens | Why it may not repeat |
| --- | --- | --- |
| Init/settings script compilation and evaluation | Determine participating builds, repositories, plugin resolution, injected support | Compiled script/cache reuse; evaluation requirements still depend on lifecycle |
| Plugin marker/module and buildscript classpath resolution | Make plugins and script imports available | Cached metadata/artifacts; unchanged resolution graph |
| Kotlin DSL early stage | Process special blocks such as `plugins` / `buildscript` to establish classpath and plugin requests | Script compilation avoidance and script caches |
| Schema/accessor generation and remaining script compilation | Type-safe accessors and script body need the established project/plugin schema | Reusable generated accessors and compiled scripts |
| buildSrc nested build | Its output supplies classes/plugins for build scripts | Up-to-date tasks or build-cache hits; compilation is conditional |
| Included build used for plugin/build logic | Requested plugin/artifact must be available to configure the consumer | Only required output tasks; caches; unrelated included-build tasks need not execute |
| Project script evaluation, plugin application and callbacks | Populate extensions, source sets, configurations, tasks and conventions | Not eliminated merely by a compiled-script cache hit |

These are dependencies in a graph, **not seven global passes over the entire build**. Settings, buildSrc, included builds, root and subprojects have their own preparation/configuration. An included build is not inherently a buildscript dependency; distinguish plugin-producing build logic from an ordinary composite dependency.

## 3. Build-logic compilation is real compilation

For a `kotlin-dsl` buildSrc, work can include external-plugin spec builders, precompiled-script plugin extraction/adapters/accessors, Kotlin compilation, resources, plugin descriptors and a JAR. Task input inspection and cache checks still happen when execution is skipped. A Kotlin compiler daemon or worker JVM may be used; the exact compilation strategy is configurable.

This checkout's [buildSrc input](../bin/inputs/buildSrc/build.gradle.kts) applies `kotlin-dsl` (`3–5`) and declares KGP and other plugin dependencies (`49–75`). The preserved baseline preflight log lists these tasks (`19–32`), **outside measured sync samples**. That log is evidence of possible build-logic work here, not its cost in a sync.

The Kotlin compiler used by Gradle's embedded Kotlin DSL, the KGP dependency used by the project/buildSrc, and IntelliJ's Kotlin support need not be the same version. Record all of them before comparing compiler or hashing costs.

## 4. Configuration can already do “model-like” work

Applying plugins creates/configures extensions, compilations and configurations. Evaluating scripts runs arbitrary build logic, including eager task access and dependency resolution if written that way. Lazy registration is not execution; reading a provider can nevertheless realize its backing objects or resolve files.

Concrete examples in this checkout:

- Root [build.gradle.kts](../bin/inputs/build.gradle.kts) declares plugin classpath dependencies (`19–29`), applies JVM/convention plugins to subprojects (`74–77`), and uses `evaluationDependsOn` for core (`94–98`). This constrains configuration ordering.
- Core [build.gradle.kts](../bin/inputs/kotlinx-coroutines-core/build.gradle.kts) declares a `benchmark` source set (`25–38`) in addition to normal compilations. A model builder may inspect more than main/test.
- Core eagerly obtains `test`, `jar`, `compileTestKotlin`, and `check` tasks (`44`, `59`, `72`, `136`). Therefore not all task realization observed during sync should be blamed on IntelliJ's builders.
- Root and buildSrc both depend on some of the same plugin artifacts. Their classpaths are distinct consumers; Gradle may reuse downloaded artifacts while still processing multiple graphs/classloaders. Deduplication needs semantic evidence, not matching dependency coordinates alone.

## 5. Cache dimensions to keep separate

| Cache/state | What it can avoid | What it does not prove |
| --- | --- | --- |
| Installed Gradle distribution | ZIP transfer/extraction | A daemon is already running |
| Daemon/classes/JIT | Process boot and some initialization/warm-up | No configuration/model work |
| Dependency metadata/artifact caches | Some network and disk generation | No graph traversal or freshness checks |
| Script/accessor caches | Recompiling unchanged Kotlin DSL | No script evaluation/plugin application |
| Task outputs/build cache | Executing build-logic compiler tasks | No input snapshot/cache-key work |
| Transform caches | Re-running identical artifact transforms | No transform lookup or different-attribute transform |
| Kotlin IC/classpath snapshots | Some compiler analysis/recompilation | Every other hashing contract can reuse those snapshots |
| Configuration/model caching | Some work on supported paths with compatible inputs | `org.gradle.configuration-cache=true` makes every IDE sync a cache hit |
| IntelliJ model/index caches | Some IDE reconstruction/index processing | Gradle state is warm |
| OS page cache/network proxies | Physical I/O/network cost | Logical operations have disappeared |

The local properties enable build/configuration caching and restrict workers to two. Actual reuse on a Tooling API model request is version/path-dependent; inspect operations and cache-hit evidence, not just the property.