# Source map and evidence limits

[Overview](../index.md) · [Machine-readable locations](../bin/source-locations.json) · [Archived excerpts](../bin/source-excerpts.json)

## Revisions and scope

| Checkout | Root | Inspected HEAD |
| --- | --- | --- |
| Kotlin | `/Users/Sebastian.Sellmair/JetBrainsProjects/kotlin` | `9303195be9d766b7f617e3b091612138fd80bc05` |
| IntelliJ ultimate | `/Volumes/JetBrainsProjects.external/ultimate` | `98cf75002093a612822a710827278ec781fa0631` |
| Import subject / evidence | `/Users/Sebastian.Sellmair/JetBrainsProjects/kotlinx.coroutines` | `3393e3f70f8cd037aa404d306e97b7c4f63daade` |

Sources were read from working trees, not checked-out pristine snapshots. Kotlin's tracked status included `.idea/inspectionProfiles/idea_default.xml`; ultimate reported no tracked changes. Untracked files were excluded from those status checks. The coroutines worktree already contained unrelated untracked benchmark/tool/environment files; they were left untouched. Archived source excerpts carry full-file SHA-256 hashes and captured tracked status.

**These revisions are not established as the revisions of the binaries used in the existing benchmarks.** Source-derived behavior is an implementation map; measured results have their own dates and version metadata.

External-repository indexed searches were unavailable/incomplete. Investigation followed known absolute paths and imports. This is not an exhaustive plugin inventory or an audit of Gradle's custom distribution internals. Android/MPP/target execution, complete indexing internals and every possible provider's concurrency/cache behavior are outside the established coverage.

## Path prefixes

The tables use these exact repository-relative prefixes to keep paths readable. `source-locations.json` expands them unambiguously; `source-excerpts.json` includes expanded paths, line ranges, hashes and the actual excerpt text.

| Prefix | Repository | Path |
| --- | --- | --- |
| `K/` | Kotlin | `libraries/tools/kotlin-gradle-plugin/src/common/kotlin/org/jetbrains/kotlin/` |
| `E/` | ultimate | `community/platform/external-system-impl/src/com/intellij/openapi/externalSystem/` |
| `G/` | ultimate | `community/plugins/gradle/src/org/jetbrains/plugins/gradle/` |
| `T/` | ultimate | `community/plugins/gradle/tooling-extension-impl/src/com/intellij/gradle/toolingExtension/impl/` |
| `I/` | ultimate | `community/plugins/gradle/tooling-extension-impl/resources/org/jetbrains/plugins/gradle/tooling/internal/init/` |
| `J/` | ultimate | `community/plugins/kotlin/gradle/gradle-java/src/org/jetbrains/kotlin/idea/gradleJava/configuration/` |
| `B/` | ultimate | `community/plugins/kotlin/gradle/gradle-tooling/impl/src/org/jetbrains/kotlin/idea/gradleTooling/` |

## Kotlin references

| ID | File and lines | Evidence anchor |
| --- | --- | --- |
| K1 | `K/gradle/plugin/KotlinCompilerArgumentsProducer.kt:17–124` | Contribution categories; default selection; lenient error handling; fresh argument creation |
| K2 | `K/gradle/tasks/KotlinCompile.kt:89–115,196–267,395–440,527–548` | Raw vs snapshot inputs; `createCompilerArguments`; file materialization; `callCompilerAsync`; `getClasspathChanges` |
| K3 | `K/gradle/internal/CompilerArgumentAware.kt:31–87` | Legacy full/default argument category selection; pre-2023.2 compatibility |
| K4 | `K/gradle/plugin/SubpluginEnvironment.kt:20–60,98–102` | Compiler artifact declarations, options and task-provider configuration |
| K5 | `K/gradle/tasks/configuration/AbstractKotlinCompileConfig.kt:94–107,150–170` | `pluginClasspath.from`; `taskProvider.configure` |
| K6 | `K/gradle/tasks/configuration/KotlinCompileConfig.kt:40–87,128–138,177–225` | Deferred `taskProvider.get().libraries`; detached snapshot configuration; transform registration guard |
| K7 | `K/gradle/internal/transforms/ClasspathEntrySnapshotTransform.kt:32–48,72–144` | Cacheable transform; classpath inputs; actual snapshot generation; granularity |
| K8 | `K/gradle/tasks/AbstractKotlinCompile.kt:231–278,311–333` | `@TaskAction`; conditional execution and compiler call |
| K9 | `K/gradle/tasks/AbstractKotlinCompileTool.kt:125–144` | Compiler-classpath validation triggers resolution |
| K10 | `K/compilerRunner/GradleCompilerRunnerWithWorkers.kt:37–80` | `noIsolation()` worker handoff |
| K11 | `K/compilerRunner/GradleKotlinCompilerWork.kt:132–186` | Daemon connection, fallback, in-process compilation |
| K12 | `K/gradle/plugin/AbstractKotlinPlugin.kt:30–86,187–193` | Java/plugin application; source-set processing; distinct named classpaths |
| K13 | `K/gradle/plugin/ide/IdeCompilerArgumentsResolver.kt:13–28` | Project-scoped `instance(project)` service |
| K14 | `K/gradle/plugin/ide/IdeCompilerArgumentsResolverImpl.kt:13–41` | Lenient primitive + plugin-classpath contributions only; argument serialization |

## Kotlin tooling builder in IntelliJ

| ID | File and lines | Evidence anchor |
| --- | --- | --- |
| B1 | `B/KotlinGradleModelBuilder.kt:40–148,164–178,200–279,298–357` | Model fields; Android-aware provider; task-object enumeration; per-source-set arguments; conditional source download |
| B2 | `B/modelBuilderUtils.kt:9–41` | Recognized targets and compilation task names |
| B3 | `B/resolveCompilerArguments.kt:10–72,79–132` | Service-present branch; legacy setup/retry/clear-classpath behavior |
| B4 | `B/reflect/KotlinCompilerArgumentsResolverReflection.kt:7–26` | Load KGP service using task classloader |
| B5 | `B/KotlinTasksPropertyUtils.kt:54–77,93–104` | Kotlin-only roots and task flags |
| B6 | `B/generatedSourceRoots.kt:13–35` | Version-gated generated-root extraction |
| B7 | `B/getAdditionalVisibleSourceSets.kt:10–20` | Visible source-set metadata |
| B8 | `community/plugins/kotlin/gradle/gradle-tooling/impl/resources/META-INF/services/org.jetbrains.plugins.gradle.tooling.ModelBuilderService:3` | Builder service registration |

## IntelliJ references

Grouped IDs in prose (for example `E08`) refer to all suffixed entries in that group.

| ID | File and lines | Evidence anchor |
| --- | --- | --- |
| E01 | `E/util/ExternalSystemUtil.java:302–444,493–570` | Refresh, `ExternalSystemSyncProjectTask`, `executeSync`, incomplete-state callback, results, before/after-sync and VFS work |
| E02 | `E/service/internal/ExternalSystemResolveProjectTask.java:69–146,174–194` | Execution settings, resolver dispatch, conditional indexing suspension, stored external structure |
| E03a | `E/service/ExternalSystemFacadeManager.java:142–197` | In-process vs remote communication manager selection |
| E03b | `G/GradleManager.java:118–198,258–265` | Distribution/JVM/download settings; resolver class |
| E04a | `G/connection/GradleConnectorFactory.kt:31–91` | Local/wrapped/target distribution connection |
| E04b | `G/connection/GradleConnectorServiceImpl.kt:69–88,164–195` | `GradleConnection` includes supplied operation; reuse predicates |
| E05 | `G/service/execution/GradleExecutionHelper.kt:79–135,172–215` | `GetModel`; initial `BuildEnvironment`; JVM/environment/listener preparation |
| E06 | `G/service/project/GradleProjectResolver.java:165–214,261–368,381–488,713–813` | Preview vs actual resolution; wrapper; injection; action; DataNodes and hierarchy passes |
| E07a | `G/service/execution/GradleInitScriptUtil.kt:78–139` | Tooling classpath and main init-script assembly |
| E07b | `I/Init.gradle:6–8` | Apply `JetGradlePlugin` |
| E07c | `I/JetGradlePlugin.gradle:24–68` | Register `ExtraModelBuilder` only if absent |
| E07d | `T/modelBuilder/ExtraModelBuilder.java:21–38,52–101,122–131` | ServiceLoader, `buildAll`, optional `idea.gradle.custom.tooling.perf` timing |
| E08a | `G/service/modelAction/GradleModelFetchActionRunner.kt:46–108` | Tooling API phased execution; streamed listener; task selection |
| E08b | `G/service/project/DefaultProjectResolverContext.java:138–202` | IDE phased/streaming predicates and version gates |
| E08c | `T/modelAction/GradleModelFetchAction.java:49–72,108–141,175–197,209–268` | Ordered phases/providers; nested builds; action context; phase state send |
| E08d | `T/modelAction/GradleDaemonModelHolder.java:93–134` | Model conversion futures; model-ID map |
| E08e | `T/util/GradleExecutorServiceUtil.kt:19–75` | Single converter, propagated context, drain with `future.get()` |
| E09a | `T/modelSerialization/ToolingSerializerConverter.java:20–37` | `SerializeGradleModel`; bytes or fallback object |
| E09b | `T/modelSerialization/ToolingSerializer.java:32–95` | Registered/default serialization services |
| E09c | `T/modelSerialization/DefaultSerializationService.java:20–37` | Java `ObjectOutputStream` and classloader-aware input |
| E09d | `G/service/modelAction/GradleIdeaModelHolder.kt:72–102` | Type-wide first-access decoding and cached replacement |
| E10a | `G/service/modelAction/GradleModelFetchActionResultHandlerBridge.kt:31–88` | Queued callbacks; one collector |
| E10b | `G/service/modelAction/GradleModelFetchActionListenerAdapter.kt:19–58` | Add state before notification; synthesized callbacks |
| E10c | `G/service/syncAction/impl/GradleSyncProjectConfigurator.kt:41–158` | Static/dynamic contributors, `lastClaimedPhase`, `${phase.name}-idea`, Workspace Model update |
| E11 | `J/KotlinGradleProjectResolverExtension.kt:83–160` | JVM builder injection; Kotlin project/source-set model; argument parsing/normalization/interning |
| E12 | `E/service/project/manage/ProjectDataManagerImpl.java:88–204,222–263,313–351,363–394,482–501` | Import lock, ordered services, post/final tasks, orphan removal, `WorkspaceModelApply` commit |
| E13 | `E/service/internal/AbstractExternalSystemTask.java:155–169` | `NOT_STARTED` transition guards a second task execution |
| E14 | `community/plugins/gradle/tooling-extension-api/src/org/jetbrains/plugins/gradle/model/ProjectImportModelProvider.java:17–70` | Default additional-model phase; no-op overloads |
| E15 | `T/util/GradleModelProviderUtil.java:23–82` | Utilities delegate to model controller |
| E16 | `T/modelAction/GradleModelControllerImpl.kt:111–218,275–309` | Target collection, sequential/parallel actions, request defaults |
| T1 | `T/telemetry/GradleOpenTelemetry.java:20–86` | `GradleDaemon` tracer, propagated context, span ending; context shutdown is not exporter flush |

## Telemetry references

All paths below are relative to ultimate; the `G/`, `T/` and `E/` prefixes above still apply. `T1` is the original general helper reference; `T09` cites narrower portions of the same file.

| ID | File and lines | Evidence anchor |
| --- | --- | --- |
| T01 | `community/plugins/gradle/plugin-resources/intellij.gradle.xml:130–132,292–293` | Execution extension; `gradle.daemon.opentelemetry.agent.enabled` default false |
| T02 | `G/service/execution/telemetry/GradleTelemetryAgentProvidingExecutionHelperExtension.kt:15–32` | Registry/endpoint/agent guards and VM-option injection |
| T03 | `community/platform/diagnostic/telemetry/src/com/intellij/platform/diagnostic/telemetry/OtlpConfiguration.kt:10–42` | Endpoint environment precedence, suffix and suppression |
| T04 | `community/platform/diagnostic/telemetry/src/com/intellij/platform/diagnostic/telemetry/OpenTelemetryUtils.kt:15–18` | `rdct.diagnostic.otlp` property |
| T05 | `community/platform/diagnostic/telemetry-impl/src/agent/TelemetryAgentProvider.kt:13–30` | Agent/config/context/service JVM options |
| T06 | `community/platform/diagnostic/telemetry-impl/src/agent/TelemetryAgentResolver.kt:23–62` | Agent 2.8.0 cache/download/hash handling |
| T07 | `community/platform/diagnostic/telemetry-impl/src/agent/AgentConfiguration.kt:22–51,100–145` | OTLP and instrumentation options; optional JSON extension |
| T08 | `community/platform/diagnostic/telemetry/rt/src/com/intellij/platform/diagnostic/telemetry/rt/context/TelemetryContext.java:15–42,62–67` | Serialized propagated context |
| T09 | `T/telemetry/GradleOpenTelemetry.java:20–27,43–73` | Daemon tracer, span end and scope-only shutdown |
| T10 | `G/service/execution/GradleExecutionHelper.kt:172–210,267–275` | Extension settings → operation JVM arguments |
| T11 | `E/util/ExternalSystemTelemetryUtil.java:19–27` | Platform external-system tracer |
| T12 | `E/diagnostic/ExternalSystemObservabilityScopes.kt:8–11` | External-system scope |
| T13 | `community/platform/diagnostic/telemetry-impl/src/TelemetryManagerImpl.kt:79–130,149–195,247–285` | SDK, W3C context, exporters, flush/shutdown |
| T14 | `community/platform/diagnostic/telemetry.exporters/src/BatchSpanProcessor.kt:38–108,112–119,130–208` | Queue, batch size, inactivity timeout, drain/export semantics |
| T15 | `community/platform/diagnostic/telemetry.exporters/src/OtlpSpanExporter.kt:18–37` | HTTP/protobuf export and errors |
| T16 | `community/platform/diagnostic/telemetry/src/com/intellij/platform/diagnostic/telemetry/AsyncSpanExporter.kt:8–16` | Default exporter flush/shutdown methods |
| T17 | `community/platform/diagnostic/telemetry-impl/src/OtlpService.kt:43–46,75–139,144–185` | Separate activity batching, timeout and stop handling |
| T18 | `community/platform/external-system-impl/resources/META-INF/ExternalSystemExtensions.xml:79–82` | Incomplete-state default true; pause-indexing default false |

## Gradle public documentation

These pages were fetched for general lifecycle/cache concepts, **not** to prove the custom 9.9 implementation. The moving `current` URLs returned older published version labels during this session.

| ID | Resource | Observed documentation version / use |
| --- | --- | --- |
| G1 | [Build lifecycle](https://docs.gradle.org/current/userguide/build_lifecycle_intermediate.html) | 9.7.1; initialization/configuration/execution distinctions |
| G2 | [Kotlin DSL primer](https://docs.gradle.org/current/userguide/kotlin_dsl.html) | 9.7.1; script compilation, caching, accessors and buildSrc invalidation |
| G3 | [Gradle daemon](https://docs.gradle.org/current/userguide/gradle_daemon.html) | 9.7.0; client/daemon split and daemon reuse |

## Local experiment evidence

- Original HTML/CSV/logs: preserved under [bin/benchmarks](../bin/README.md), with original paths/hashes in [raw-file-manifest.json](../bin/raw-file-manifest.json).
- Current scenario/configuration/build-script inputs: preserved under `bin/inputs`, **not** asserted to be the historical inputs for each report.
- Existing capture helper documentation: `tools/gradle-import-profile/README.md:72–92,121–139,157–170` describes its distinct timing/indexing controls and output files. It was not executed.
- User-supplied OTel recipe: retained with its assumptions and adaptation in [telemetry collection](../telemetry/collection.md). Local read-only HTTP checks found neither Jaeger UI nor the OTLP receiver listening; no local capture was run.
- Subsequently supplied Jaeger export: `import-benchmarks/yahor/traces-1789726526259.json`, preserved with SHA-256 and analyzed independently in [the measured timeline](../measurements/jaeger-trace.md). Its runtime versions/cache state are not inferred from these source checkouts.