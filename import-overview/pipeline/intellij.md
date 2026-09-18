# IntelliJ: requesting, transporting and applying models

[Overview](../index.md) · [Kotlin details](kotlin-models.md) · [Source map](../reference/sources.md)

References `E01`–`E13` below identify inspected source locations, not measured durations.

## Refresh and environment discovery

`ExternalSystemUtil.refreshProjectImpl` saves documents, creates `ExternalSystemResolveProjectTask`, and enters `ExternalSystemSyncProjectTask`. Before-sync tasks can execute before resolution. The task obtains execution settings and dispatches through the external-system facade ([E01–E03](../reference/sources.md)).

The facade architecture supports in-process and remote communication; do not infer a mandatory helper JVM from a `Remote...` interface name. The effective Gradle/target-specific process selection was not fully traced. The separate Gradle daemon is the important established execution boundary.

`GradleConnectorFactory` selects local/wrapped/target connections. `GradleConnectorServiceImpl` caches connections by project path subject to compatible parameters, a non-null Gradle home and a non-target connector ([E04](../reference/sources.md)). This saves connection setup; it is **not proof of cross-sync model reuse**.

Before the main action, `GradleExecutionHelper.execute` requests **`BuildEnvironment`**, checks it, then invokes the resolver callback. The `GetModel` span records the model class. Operation preparation applies JVM/Gradle arguments, environment, Java home, listeners, streams and cancellation ([E05](../reference/sources.md)). A trace with multiple Tooling API requests does not automatically show duplicate project-model requests.

## Inject tooling before requesting its models

`GradleProjectResolver` constructs its resolver chain, gathers model providers and extra classes, performs pre-import checks, and creates main/mapper init scripts. The main script brings tooling/telemetry classes onto its classpath and applies `JetGradlePlugin`; that plugin registers `ExtraModelBuilder` **if absent**. `ExtraModelBuilder` discovers services with `ServiceLoader` and dispatches `buildAll` by supported model name ([E06–E07](../reference/sources.md)).

The IDE therefore supplies code, but Gradle runs the builder against its own projects, tasks and configurations. KGP supplies the task/argument APIs the Kotlin builder can inspect. Multiple included builds, service classloaders and older-version compatibility branches add work; “inject builder” is not a new operation for each model instance.

## Several meanings of “phase”

| Mechanism | What the inspected source does |
| --- | --- |
| Gradle lifecycle | Initialization/configuration and conditional task execution; see [preparation](gradle-preparation.md) |
| Tooling API phased action | On Gradle 4.8+, uses `projectsLoaded` and `buildFinished`; older Gradle uses the default action path |
| Model-provider phases | Ordered phase map; providers grouped with a `LinkedHashSet`; project-loaded and build-finished work partitioned |
| Streamed intermediate state | Optional `buildController.send(phasedState)` delivers additional partial results |
| IDE sync contributors | Static contributors at resolve start; dynamic contributors on model callbacks, including early Workspace Model updates |

These are not interchangeable. In the inspected revision, streaming requires an open project, the phased-sync flag, Gradle 8.6+, and excludes isolated-project mode below 8.9. IDE phased eligibility has additional module/source-set/name conditions. Treat these thresholds as **this revision's implementation**, not a promise for all IDE releases ([E08](../reference/sources.md)).

The runner uses `forTasks(emptyList())`, but its comment notes builders can set task names. No explicit application task request is not a guarantee that no buildSrc/included-build/plugin-requested task executes.

## Model construction, conversion and transport overlap

`GradleModelFetchAction` establishes root/nested build information and model storage, invokes the providers in phase order, and retains state across the Tooling API phases. The shared model controller supports sequential requests or `BuildController.run` over per-target actions; default mode follows `isParallelModelFetchEnabled()`. Its default request targets projects from each supplied build's `projects` collection ([E14–E16](../reference/sources.md)). Actual parallel scheduling still depends on Gradle. Calling both provider compatibility overloads is not itself duplication: the interface defaults are no-ops, and the Kotlin provider overrides only the raw-controller form.

`GradleDaemonModelHolder` submits model conversion to a **single conversion executor**. Model production can overlap that executor's work. Draining a phase calls `future.get()`, so sending a partial result may wait for serialization ([E08](../reference/sources.md)). Useful measurements are serialization CPU/bytes plus queue and phase-boundary wait, not just model-builder duration.

The transport has two layers ([E09](../reference/sources.md)):

1. **Model encoding:** registered serialization services can encode models. The default service uses `ObjectOutputStream.writeObject`, producing bytes; unsupported conversion can fall back to the object.
2. **Tooling API transport:** the enclosing result/streamed state crosses the client/daemon boundary. These sources do not establish the entire Gradle wire protocol as Java serialization.

On the IDE side, `GradleIdeaModelHolder` returns objects already converted; otherwise the first access converts **all stored models of the requested type**, then caches the replacements. This is a plausible eager-decoding cost, not repeated decoding on every access.

## Two project-model application paths coexist

**Early/phased path:** result callbacks enqueue events in an unlimited channel; one collector dispatches them. The listener adds models before notifying contributors. `GradleSyncProjectConfigurator` claims phases once using `lastClaimedPhase`, constructs contributor models, calls `workspaceModel.update`, updates bridges and notifies listeners ([E10](../reference/sources.md)). Overlapping callback ranges do not prove duplicated contributor execution.

**DataNode path:** after model acquisition/event collection, `GradleProjectResolverDataProcessing` extracts build/project hierarchy and associates source-set, task and dependency models. `convertData` builds project/module nodes, content roots, output paths, task data and dependencies through resolver extensions ([E06](../reference/sources.md)).

The Kotlin/JVM extension injects its tooling builder, retrieves `KotlinGradleModel`, creates Kotlin project/source-set nodes, parses compiler arguments, normalizes paths, interns large arguments and records the plugin version. Its multiplatform branch returns separately ([E11](../reference/sources.md)).

`ProjectDataManagerImpl` serializes import entry with a lock, recursively groups nodes, orders data keys, invokes data services, removes orphaned data as needed, runs post-processing and final tasks, and commits through the models provider. Workspace services receive mutable entity storage; other services use the legacy bridge. `WorkspaceModelApply` surrounds the commit inside a project-change action ([E12](../reference/sources.md)). Not every preceding conversion operation is on the UI thread, and this span is not a timer for the whole import.

## Completion and background work

Result handling may import successful **or partial** data, call success/failure callbacks, run after-sync tasks, refresh new-project files, and dispatch completion. The resolver can suspend scanning/indexing under `external.system.pause.indexing.during.sync`; otherwise background work can overlap it ([E01–E02](../reference/sources.md)).

Record separately:

- external-system sync span completion;
- final model application/callback completion;
- VFS refresh and scanning completion;
- indexing completion / readiness for the intended editor operation.

The inspected path does not establish that the first waits for all of the others. Cancellation, unresolved dependencies and partial imports must be retained in measurements, not silently treated as successful fast syncs.

## Particularly concrete duplication candidate

At this revision, `ExternalSystemUtil.incompleteDependenciesState` calls its runnable when `external.system.incomplete.dependencies.state.during.sync` is false, then falls through and calls it again inside the incomplete-state scope. This can repeat the surrounding sync-result/import/callback path if the first call returns normally ([E01, E13](../reference/sources.md)). **The declared default is true**, so this requires a nondefault setting ([T18](../reference/sources.md)); it is not asserted for ordinary default syncs.

**It does not establish two Gradle builds:** `AbstractExternalSystemTask.execute` guards the task's transition out of `NOT_STARTED`, so a second execute attempt is skipped. Count before/after-sync hooks, imports and callbacks separately. This is a source-backed conditional finding, not reproduced behavior in the supplied benchmark runs; no code was changed here. See [candidate D1](../analysis/duplication.md).