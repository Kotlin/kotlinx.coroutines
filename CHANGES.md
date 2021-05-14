# Change log for kotlinx.coroutines

## Version 1.5.0

Note that this is a full changelog relative to 1.4.3 version. Changelog relative to 1.5.0-RC can be found in the end.

### Channels API

* Major channels API rework (#330, #974). Existing `offer`, `poll`, and `sendBlocking` methods are deprecated, internal `receiveCatching` and `onReceiveCatching` removed, `receiveOrNull` and `onReceiveOrNull` are completely deprecated. Previously deprecated `SendChannel.isFull` declaration is removed. Channel operators deprecated with `ERROR` are now `HIDDEN`.
* New methods `receiveCatching`, `onReceiveCatching` `trySend`, `tryReceive`, and `trySendBlocking` along with the new result type `ChannelResult` are introduced. They provide better type safety, are less error-prone, and have a consistent future-proof naming scheme.  The full rationale behind this change can be found [here](https://github.com/Kotlin/kotlinx.coroutines/issues/974#issuecomment-806569582).
* `BroadcastChannel` and `ConflatedBroadcastChannel` are marked as `ObsoleteCoroutinesApi` in the favor or `SharedFlow` and `StateFlow`. The migration scheme can be found in their documentation. These classes will be deprecated in the next major release.
* `callbackFlow` and `channelFlow` are promoted to stable API.

### Reactive integrations

* All existing API in modules `kotlinx-coroutines-rx2`, `kotlinx-coroutines-rx3`, `kotlinx-coroutines-reactive`, `kotlinx-coroutines-reactor`, and `kotlinx-coroutines-jdk9` were revisited and promoted to stable (#2545).
* `publish` is no longer allowed to emit `null` values (#2646).
* Misleading `awaitSingleOr*` functions on `Publisher` type are deprecated (#2591).
* `MaybeSource.await` is deprecated in the favor of `awaitSingle`, additional lint functions for `Mono` are added in order to prevent ambiguous `Publisher` usages (#2628, #1587).
* `ContextView` support in `kotlinx-coroutines-reactor` (#2575).
* All reactive builders no longer ignore inner cancellation exceptions preventing their completion (#2262, #2646).
* `MaybeSource.collect` and `Maybe.collect` properly finish when they are completed without a value (#2617).
* All exceptions are now consistently handled according to reactive specification, whether they are considered 'fatal' or not by reactive frameworks (#2646).

### Other improvements

* Kotlin version is upgraded to 1.5.0 and JVM target is updated to 1.8.
* `Flow.last` and `Flow.lastOrNull` operators (#2246).
* `Flow.runningFold` operator (#2641).
* `CoroutinesTimeout` rule for JUnit5 (#2197).
* Internals of `Job` and `AbstractCoroutine` was reworked, resulting in smaller code size, less memory footprint, and better performance (#2513, #2512).
* `CancellationException` from Kotlin standard library is used for cancellation on Koltin/JS and Kotlin/Native (#2638).
* Introduced new `DelicateCoroutinesApi` annotation that warns users about potential target API pitfalls and suggests studying API's documentation first. The only delicate API right now is `GlobalScope` (#2637).
* Fixed bug introduced in `1.4.3` when `kotlinx-coroutines-core.jar` triggered IDEA debugger failure (#2619).
* Fixed memory leak of `ChildHandlerNode` with reusable continuations (#2564).
* Various documentation improvements (#2555, #2589, #2592, #2583, #2437, #2616, #2633, #2560).

### Changelog relative to version 1.5.0-RC

* Fail-fast during `emitAll` called from cancelled `onCompletion` operator (#2700).
* Flows returned by `stateIn`/`shareIn` keep strong reference to sharing job (#2557).
* Rename internal `TimeSource` to `AbstractTimeSource` due to import issues (#2691).
* Reverted the change that triggered IDEA coroutines debugger crash (#2695, reverted #2291).
* `watchosX64` target support for Kotlin/Native (#2524).
* Various documentation fixes and improvements.

## Version 1.5.0-RC

### Channels API

* Major channels API rework (#330, #974). Existing `offer`, `poll`, and `sendBlocking` methods are deprecated, internal `receiveCatching` and `onReceiveCatching` removed, `receiveOrNull` and `onReceiveOrNull` are completely deprecated. Previously deprecated `SendChannel.isFull` declaration is removed. Channel operators deprecated with `ERROR` are now `HIDDEN`.
* New methods `receiveCatching`, `onReceiveCatching` `trySend`, `tryReceive`, and `trySendBlocking` along with the new result type `ChannelResult` are introduced. They provide better type safety, are less error-prone, and have a consistent future-proof naming scheme.  The full rationale behind this change can be found [here](https://github.com/Kotlin/kotlinx.coroutines/issues/974#issuecomment-806569582).
* `BroadcastChannel` and `ConflatedBroadcastChannel` are marked as `ObsoleteCoroutinesApi` in the favor or `SharedFlow` and `StateFlow`. The migration scheme can be found in their documentation. These classes will be deprecated in the next major release.
* `callbackFlow` and `channelFlow` are promoted to stable API.

### Reactive integrations

* All existing API in modules `kotlinx-coroutines-rx2`, `kotlinx-coroutines-rx3`, `kotlinx-coroutines-reactive`, `kotlinx-coroutines-reactor`, and `kotlinx-coroutines-jdk9` were revisited and promoted to stable (#2545).
* `publish` is no longer allowed to emit `null` values (#2646).
* Misleading `awaitSingleOr*` functions on `Publisher` type are deprecated (#2591).
* `MaybeSource.await` is deprecated in the favor of `awaitSingle`, additional lint functions for `Mono` are added in order to prevent ambiguous `Publisher` usages (#2628, #1587).
* `ContextView` support in `kotlinx-coroutines-reactor` (#2575).
* All reactive builders no longer ignore inner cancellation exceptions preventing their completion (#2262, #2646).
* `MaybeSource.collect` and `Maybe.collect` properly finish when they are completed without a value (#2617).
* All exceptions are now consistently handled according to reactive specification, whether they are considered 'fatal' or not by reactive frameworks (#2646).

### Other improvements

* `Flow.last` and `Flow.lastOrNull` operators (#2246).
* `Flow.runningFold` operator (#2641).
* `CoroutinesTimeout` rule for JUnit5 (#2197).
* Internals of `Job` and `AbstractCoroutine` was reworked, resulting in smaller code size, less memory footprint, and better performance (#2513, #2512).
* `CancellationException` from Kotlin standard library is used for cancellation on Koltin/JS and Kotlin/Native (#2638).
* Introduced new `DelicateCoroutineApi` annotation that warns users about potential target API pitfalls and suggests studying API's documentation first. The only delicate API right now is `GlobalScope` (#2637).
* Fixed bug introduced in `1.4.3` when `kotlinx-coroutines-core.jar` triggered IDEA debugger failure (#2619).
* Fixed memory leak of `ChildHandlerNode` with reusable continuations (#2564).
* Various documentation improvements (#2555, #2589, #2592, #2583, #2437, #2616, #2633, #2560).

## Version 1.4.3 

### General changes

* Thread context is properly preserved and restored for coroutines without `ThreadContextElement` (#985)
* `ThreadContextElement`s are now restored in the opposite order from update (#2195)
* Improved performance of combine with 4 parameters, thanks to @alexvanyo (#2419)
* Debug agent sanitizer leaves at least one frame with source location (#1437)
* Update Reactor version in `kotlinx-coroutines-reactor` to `3.4.1`, thanks to @sokomishalov (#2432)
* `callInPlace` contract added to `ReceiveChannel.consume` (#941)
* `CoroutineStart.UNDISPATCHED` promoted to stable API (#1393)
* Kotlin updated to 1.4.30
* `kotlinx.coroutines` are now released directly to MavenCentral  
* Reduced the size of `DispatchedCoroutine` by a field
* Internal class `TimeSource` renamed to `SchedulerTimeSource` to prevent wildcard import issues (#2537)

### Bug fixes

* Fixed the problem that prevented implementation via delegation for `Job` interface (#2423)
* Fixed incorrect ProGuard rules that allowed shrinking volatile felds (#1564)
* Fixed `await`/`asDeferred` for `MinimalStage` implementations in jdk8 module (#2456)
* Fixed bug when `onUndeliveredElement` wasn't called for unlimited channels (#2435)
* Fixed a bug when `ListenableFuture.isCancelled` returned from `asListenableFuture` could have thrown an exception, thanks to @vadimsemenov (#2421)
* Coroutine in `callbackFlow` and `produce` is properly cancelled when the channel was closed separately (#2506)

## Version 1.4.2

* Fixed `StackOverflowError` in `Job.toString` when `Job` is observed in its intermediate state (#2371).
* Improved liveness and latency of `Dispatchers.Default` and `Dispatchers.IO` in low-loaded mode (#2381).
* Improved performance of consecutive `Channel.cancel` invocations (#2384).
* `SharingStarted` is now `fun` interface (#2397).
* Additional lint settings for `SharedFlow` to catch programmatic errors early (#2376).
* Fixed bug when mutex and semaphore were not released during cancellation (#2390, thanks to @Tilps for reproducing).
* Some corner cases in cancellation propagation between coroutines and listenable futures are repaired (#1442, thanks to @vadimsemenov).
* Fixed unconditional cast to `CoroutineStackFrame` in exception recovery that triggered failures of instrumented code (#2386).
* Platform-specific dependencies are removed from `kotlinx-coroutines-javafx` (#2360). 

## Version 1.4.1

This is a patch release with an important fix to the `SharedFlow` implementation.

* SharedFlow: Fix scenario with concurrent emitters and cancellation of subscriber (#2359, thanks to @vehovsky for the bug report).

## Version 1.4.0

### Improvements

* `StateFlow`, `SharedFlow` and corresponding operators are promoted to stable API (#2316).
* `Flow.debounce` operator with timeout selector based on each individual element is added (#1216, thanks to @mkano9!). 
* `CoroutineContext.job` extension property is introduced (#2159).
* `Flow.combine operator` is reworked:
    * Complete fairness is maintained for single-threaded dispatchers.
    * Its performance is improved, depending on the use-case, by at least 50% (#2296).
    * Quadratic complexity depending on the number of upstream flows is eliminated (#2296).
    * `crossinline` and `inline`-heavy internals are removed, fixing sporadic SIGSEGV on Mediatek Android devices (#1683, #1743).
* `Flow.zip` operator performance is improved by 40%.
* Various API has been promoted to stable or its deprecation level has been raised (#2316).

### Bug fixes

* Suspendable `stateIn` operator propagates exception to the caller when upstream fails to produce initial value (#2329).
* Fix `SharedFlow` with replay for subscribers working at different speed (#2325).
* Do not fail debug agent installation when security manager does not provide access to system properties (#2311).
* Cancelled lazy coroutines are properly cleaned up from debug agent output (#2294).
* `BlockHound` false-positives are correctly filtered out (#2302, #2190, #2303).
* Potential crash during a race between cancellation and upstream in `Observable.asFlow` is fixed (#2104, #2299, thanks to @LouisCAD and @drinkthestars).

## Version 1.4.0-M1

### Breaking changes

* The concept of atomic cancellation in channels is removed. All operations in channels
    and corresponding `Flow` operators are cancellable in non-atomic way (#1813).
* If `CoroutineDispatcher` throws `RejectedExecutionException`, cancel current `Job` and schedule its execution to `Dispatchers.IO` (#2003).
* `CancellableContinuation.invokeOnCancellation` is invoked if the continuation was cancelled while its resume has been dispatched (#1915).
* `Flow.singleOrNull` operator is aligned with standard library and does not longer throw `IllegalStateException` on multiple values (#2289). 

### New experimental features

* `SharedFlow` primitive for managing hot sources of events with support of various subscription mechanisms, replay logs and buffering (#2034).
* `Flow.shareIn` and `Flow.stateIn` operators to transform cold instances of flow to hot `SharedFlow` and `StateFlow` respectively (#2047).

### Other
    
* Support leak-free closeable resources transfer via `onUndeliveredElement` in channels (#1936).
* Changed ABI in reactive integrations for Java interoperability (#2182).
* Fixed ProGuard rules for `kotlinx-coroutines-core` (#2046, #2266).
* Lint settings were added to `Flow` to avoid accidental capturing of outer `CoroutineScope` for cancellation check (#2038). 

### External contributions

* Allow nullable types in `Flow.firstOrNull` and `Flow.singleOrNull` by @ansman (#2229).
* Add `Publisher.awaitSingleOrDefault|Null|Else` extensions by @sdeleuze (#1993).
* `awaitCancellation` top-level function by @LouisCAD (#2213).
* Significant part of our Gradle build scripts were migrated to `.kts` by @turansky. 

Thank you for your contributions and participation in the Kotlin community!

## Version 1.3.9

* Support of `CoroutineContext` in `Flow.asPublisher` and similar reactive builders (#2155).
* Kotlin updated to 1.4.0.
* Transition to new HMPP publication scheme for multiplatform usages:
    * Artifacts `kotlinx-coroutines-core-common` and `kotlinx-coroutines-core-native` are removed.
    * For multiplatform usages, it's enough to [depend directly](README.md#multiplatform) on `kotlinx-coroutines-core` in `commonMain` source-set.
    * The same artifact coordinates can be used to depend on platform-specific artifact in platform-specific source-set.

## Version 1.3.8

### New experimental features

* Added `Flow.transformWhile operator` (#2065).
* Replaced `scanReduce` with `runningReduce` to be consistent with the Kotlin standard library (#2139).

### Bug fixes and improvements

* Improve user experience for the upcoming coroutines debugger (#2093, #2118, #2131).
* Debugger no longer retains strong references to the running coroutines (#2129).
* Fixed race in `Flow.asPublisher` (#2109).
* Fixed `ensureActive` to work in the empty context case to fix `IllegalStateException` when using flow from `suspend fun main` (#2044).
* Fixed a problem with `AbortFlowException` in the `Flow.first` operator to avoid erroneous `NoSuchElementException` (#2051).
* Fixed JVM dependency on Android annotations (#2075).
* Removed keep rules mentioning `kotlinx.coroutines.android` from core module (#2061 by @mkj-gram).
* Corrected some docs and examples (#2062, #2071, #2076, #2107, #2098, #2127, #2078, #2135).                                                                          
* Improved the docs and guide on flow cancellation (#2043).
* Updated Gradle version to `6.3` (it only affects multiplatform artifacts in this release).

## Version 1.3.7

* Fixed problem that triggered Android Lint failure (#2004).
* New `Flow.cancellable()` operator for cooperative cancellation (#2026).
* Emissions from `flow` builder now check cancellation status and are properly cancellable (#2026).
* New `currentCoroutineContext` function to use unambiguously in the contexts with `CoroutineScope` in receiver position (#2026). 
* `EXACTLY_ONCE` contract support in coroutine builders.
* Various documentation improvements.

## Version 1.3.6

### Flow

* `StateFlow`, new primitive for state handling (#1973, #1816, #395). The `StateFlow` is designed to eventually replace `ConflatedBroadcastChannel` for state publication scenarios. Please, try it and share your feedback. Note, that Flow-based primitives to publish events will be added later. For events you should continue to either use `BroadcastChannel(1)`, if you put events into the `StateFlow`, protect them from double-processing with flags.
* `Flow.onEmpty` operator is introduced (#1890).
* Behavioural change in `Flow.onCompletion`, it is aligned with `invokeOnCompletion` now and passes `CancellationException` to its cause parameter (#1693).
* A lot of Flow operators have left its experimental status and are promoted to stable API.

### Other

* `runInterruptible` primitive to tie cancellation with thread interruption for blocking calls. Contributed by @jxdabc (#1947).
* Integration module with RxJava3 is introduced. Contributed by @ZacSweers (#1883)
* Integration with [BlockHound](https://github.com/reactor/BlockHound) in `kotlinx-coroutines-debug` module (#1821, #1060).
* Memory leak in ArrayBroadcastChannel is fixed (#1885).
* Behavioural change in `suspendCancellableCoroutine`, cancellation is established before invoking passed block argument (#1671).
* Debug agent internals are moved into `kotlinx-coroutines-core` for better integration with IDEA. It should not affect library users and all the redundant code should be properly eliminated with R8.
* ClassCastException with reusable continuations bug is fixed (#1966).
* More precise scheduler detection for `Executor.asCoroutineDispatcher` (#1992).
* Kotlin updated to 1.3.71.

## Version 1.3.5

* `firstOrNull` operator. Contributed by @bradynpoulsen.
* `java.time` adapters for Flow operators. Contributed by @fvasco.
* `kotlin.time.Duration` support (#1402). Contributed by @fvasco. 
* Memory leak with a mix of reusable and non-reusable continuations is fixed (#1855).
* `DebugProbes` are ready for production installation: its performance is increased, the flag to disable creation stacktraces to reduce the footprint is introduced (#1379, #1372).
* Stacktrace recovery workaround for Android 6.0 and earlier bug (#1866).
* New integration module: `kotlinx-coroutines-jdk9` with adapters for `java.util.concurrent.Flow`.
* `BroadcastChannel.close` properly starts lazy coroutine (#1713).
* `kotlinx-coroutines-bom` is published without Gradle metadata.
* Make calls to service loader in reactor integrations optimizable by R8 (#1817).

## Version 1.3.4

### Flow

* Detect missing `awaitClose` calls in `callbackFlow` to make it less error-prone when used with callbacks (#1762, #1770). This change makes `callbackFlow` **different** from `channelFlow`.
* `ReceiveChannel.asFlow` extension is introduced (#1490).
* Enforce exception transparency invariant in `flow` builder (#1657).
* Proper `Dispatcher` support in `Flow` reactive integrations (#1765).
* Batch `Subscription.request` calls in `Flow` reactive integration (#766).
* `ObservableValue.asFlow` added to JavaFx integration module (#1695).
* `ObservableSource.asFlow` added to RxJava2 integration module (#1768).

### Other changes

* `kotlinx-coroutines-core` is optimized for R8, making it much smaller for Android usages (75 KB for `1.3.4` release).
* Performance of `Dispatchers.Default` is improved (#1704, #1706).
* Kotlin is updated to 1.3.70.
* `CoroutineDispatcher` and `ExecutorCoroutineDispatcher` experimental coroutine context keys are introduced (#1805).
* Performance of various `Channel` operations is improved (#1565).

## Version 1.3.3

### Flow
* `Flow.take` performance is significantly improved (#1538).
* `Flow.merge` operator (#1491).
* Reactive Flow adapters are promoted to stable API (#1549).
* Reusable cancellable continuations were introduced that improved the performance of various flow operators and iteration over channels (#1534).
* Fixed interaction of multiple flows with `take` operator (#1610).
* Throw `NoSuchElementException` instead of `UnsupportedOperationException` for empty `Flow` in `reduce` operator (#1659).
* `onCompletion` now rethrows downstream exceptions on emit attempt (#1654).
* Allow non-emitting `withContext` from `flow` builder (#1616).

### Debugging

* `DebugProbes.dumpCoroutines` is optimized to be able to print the 6-digit number of coroutines (#1535).
* Properly capture unstarted lazy coroutines in debugger (#1544).
* Capture coroutines launched from within a test constructor with `CoroutinesTimeout` test rule (#1542).
* Stacktraces of `Job`-related coroutine machinery are shortened and prettified (#1574).
* Stacktrace recovery unification that should provide a consistent experience recover of stacktrace (#1597).
* Stacktrace recovery for `withTimeout` is supported (#1625).
* Do not recover exception with a single `String` parameter constructor that is not a `message` (#1631).

### Other features

* `Dispatchers.Default` and `Dispatchers.IO` rework: CPU consumption is significantly lower, predictable idle threads termination (#840, #1046, #1286).
* Avoid `ServiceLoader` for loading `Dispatchers.Main` (#1572, #1557, #878, #1606).
* Consistently handle undeliverable exceptions in RxJava and Reactor integrations (#252, #1614).
* `yield` support in immediate dispatchers (#1474).
* `CompletableDeferred.completeWith(result: Result<T>)` is introduced.
* Added support for tvOS and watchOS-based Native targets (#1596).

### Bug fixes and improvements

* Kotlin version is updated to 1.3.61.
* `CoroutineDispatcher.isDispatchNeeded` is promoted to stable API (#1014).
* Livelock and stackoverflows in mutual `select` expressions are fixed (#1411, #504).
* Properly handle `null` values in `ListenableFuture` integration (#1510).
* Making ReceiveChannel.cancel linearizability-friendly.
* Linearizability of Channel.close in a complex contended cases (#1419).
* ArrayChannel.isBufferEmpty atomicity is fixed (#1526).
* Various documentation improvements.
* Reduced bytecode size of `kotlinx-coroutines-core`, reduced size of minified `dex` when using basic functionality of `kotlinx-coroutines`.

## Version 1.3.2

This is a maintenance release that does not include any new features or bug fixes.

* Reactive integrations for `Flow` are promoted to stable API.
* Obsolete reactive API is deprecated.
* Deprecation level for API deprecated in 1.3.0 is increased.
* Various documentation improvements.

## Version 1.3.1

This is a minor update with various fixes:
* Flow: Fix recursion in combineTransform<T1, T2, R> (#1466).
* Fixed race in the Semaphore (#1477).
* Repaired some of ListenableFuture.kt's cancellation corner cases (#1441).
* Consistently unwrap exception in slow path of CompletionStage.asDeferred (#1479).
* Various fixes in documentation (#1496, #1476, #1470, #1468).
* Various cleanups and additions in tests.

Note: Kotlin/Native artifacts are now published with Gradle metadata format version 1.0, so you will need 
Gradle version 5.3 or later to use this version of kotlinx.coroutines in your Kotlin/Native project.

## Version 1.3.0

### Flow

This version is the first stable release with [`Flow`](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow/index.html) API.

All `Flow` API not marked with `@FlowPreview` or `@ExperimentalCoroutinesApi` annotations are stable and here to stay.
Flow declarations marked with `@ExperimentalCoroutinesApi` have [the same guarantees](/docs/topics/compatibility.md#experimental-api) as regular experimental API.
Please note that API marked with `@FlowPreview` have [weak guarantees](/docs/topics/compatibility.md#flow-preview-api) on source, binary and semantic compatibility.

### Changelog

* A new [guide section](/docs/topics/flow.md) about Flow.
* `CoroutineDispatcher.asExecutor` extension (#1450).
* Fixed bug when `select` statement could report the same exception twice (#1433).
* Fixed context preservation in `flatMapMerge` in a case when collected values were immediately emitted to another flow (#1440).
* Reactive Flow integrations enclosing files are renamed for better interoperability with Java.
* Default buffer size in all Flow operators is increased to 64.
* Kotlin updated to 1.3.50.

## Version 1.3.0-RC2

### Flow improvements
* Operators for UI programming are reworked for the sake of consistency, naming scheme for operator overloads is introduced:
   * `combineLatest` is deprecated in the favor of `combine`.
   * `combineTransform` operator for non-trivial transformations (#1224).
   * Top-level `combine` and `combineTransform` overloads for multiple flows (#1262). 
   * `switchMap` is deprecated. `flatMapLatest`, `mapLatest` and `transformLatest` are introduced instead (#1335).
   * `collectLatest` terminal operator (#1269).

* Improved cancellation support in `flattenMerge` (#1392).
* `channelFlow` cancellation does not leak to the parent (#1334).
* Fixed flow invariant enforcement for `suspend fun main` (#1421).
* `delayEach` and `delayFlow` are deprecated (#1429).

### General changes
* Integration with Reactor context
    * Propagation of the coroutine context of `await` calls into Mono/Flux builder.
    * Publisher.asFlow propagates coroutine context from `collect` call to the Publisher.
    * New `Flow.asFlux ` builder.

* ServiceLoader-code is adjusted to avoid I/O on the Main thread on newer (3.6.0+) Android toolchain.
* Stacktrace recovery support for minified builds on Android (#1416).
* Guava version in `kotlinx-coroutines-guava` updated to `28.0`.
* `setTimeout`-based JS dispatcher for platforms where `process` is unavailable (#1404).
* Native, JS and common modules are added to `kotlinx-coroutines-bom`.
* Fixed bug with ignored `acquiredPermits` in `Semaphore` (#1423).

## Version 1.3.0-RC

### Flow

* Core `Flow` API is promoted to stable
* New basic `Flow` operators: `withIndex`, `collectIndexed`, `distinctUntilChanged` overload
* New core `Flow` operators: `onStart` and `onCompletion`
* `ReceiveChannel.consumeAsFlow` and `emitAll` (#1340)

### General changes

* Kotlin updated to 1.3.41
* Added `kotlinx-coroutines-bom` with Maven Bill of Materials (#1110)
* Reactive integrations are seriously improved
  * All builders now are top-level functions instead of extensions on `CoroutineScope` and prohibit `Job` instance in their context to simplify lifecycle management
  * Fatal exceptions are handled consistently (#1297)
  * Integration with Reactor Context added (#284)
* Stacktrace recovery for `suspend fun main` (#1328)
* `CoroutineScope.cancel` extension with message (#1338)
* Protection against non-monotonic clocks in `delay` (#1312)
* `Duration.ZERO` is handled properly in JDK 8 extensions (#1349)
* Library code is adjusted to be more minification-friendly 

## Version 1.3.0-M2

 * Kotlin updated to 1.3.40.
 * `Flow` exception transparency concept.
 * New declarative `Flow` operators: `onCompletion`, `catch`, `retryWhen`, `launchIn`. `onError*` operators are deprecated in favour of `catch`. (#1263)
 * `Publisher.asFlow` is integrated with `buffer` operator.
 * `Publisher.openSubscription` default request size is `1` instead of `0` (#1267).

## Version 1.3.0-M1

Flow:
 * Core `Flow` interfaces and operators are graduated from preview status to experimental. 
 * Context preservation invariant rework (#1210).
    * `channelFlow` and `callbackFlow` replacements for `flowViaChannel` for concurrent flows or callback-based APIs.
    * `flow` prohibits emissions from non-scoped coroutines by default and recommends to use `channelFlow` instead to avoid most of the concurrency-related bugs.
 * Flow cannot be implemented directly 
    * `AbstractFlow` is introduced for extension (e.g. for managing state) and ensures all context preservation invariants.
 * Buffer size is decoupled from all operators that imply channel usage (#1233)
    * `buffer` operator can be used to adjust buffer size of any buffer-dependent operator (e.g. `channelFlow`, `flowOn` and `flatMapMerge`).
    * `conflate` operator is introduced.
 * Flow performance is significantly improved.
 * New operators: `scan`, `scanReduce`, `first`, `emitAll`.
 * `flowWith` and `flowViaChannel` are deprecated.
 * `retry` ignores cancellation exceptions from upstream when the flow was externally cancelled (#1122).
 * `combineLatest` overloads for multiple flows (#1193).
 * Fixed numerical overflow in `drop` operator.

Channels:
 * `consumeEach` is promoted to experimental API (#1080).
 * Conflated channels always deliver the latest value after closing (#332, #1235).
 * Non-suspending `ChannelIterator.next` to improve iteration performance (#1162).
 * Channel exception types are consistent with `produce` and are no longer swallowed as cancellation exceptions in case of programmatic errors (#957, #1128).
 * All operators on channels (that were prone to coroutine leaks) are deprecated in the favor of `Flow`.

General changes:
 * Kotlin updated to 1.3.31
 * `Semaphore` implementation (#1088)
 * Loading of `Dispatchers.Main` is tweaked so the latest version of R8 can completely remove I/O when loading it (#1231).
 * Performace of all JS dispatchers is significantly improved (#820).
 * `withContext` checks cancellation status on exit to make reasoning about sequential concurrent code easier (#1177).
 * Consistent exception handling mechanism for complex hierarchies (#689).
 * Convenient overload for `CoroutinesTimeout.seconds` (#1184).
 * Fix cancellation bug in onJoin (#1130).
 * Prevent internal names clash that caused errors for ProGuard (#1159).
 * POSIX's `nanosleep` as `delay` in `runBlocking ` in K/N (#1225).

## Version 1.2.2

* Kotlin updated to 1.3.40.

## Version 1.2.1

Major:
  * Infrastructure for testing coroutine-specific code in `kotlinx-coroutines-test`: `runBlockingTest`, `TestCoroutineScope` and `TestCoroutineDispatcher`, contributed by Sean McQuillan (@objcode). Obsolete `TestCoroutineContext` from `kotlinx-coroutines-core` is deprecated.
  * `Job.asCompletableFuture` extension in jdk8 module (#1113).

Flow improvements:
  * `flowViaChannel` rework: block parameter is no longer suspending, but provides `CoroutineScope` receiver and allows conflated channel (#1081, #1112).
  * New operators: `switchMap`, `sample`, `debounce` (#1107).
  * `consumerEach` is deprecated on `Publisher`, `ObservableSource` and `MaybeSource`, `collect` extension is introduced instead (#1080).

Other:
  * Race in Job.join and concurrent cancellation is fixed (#1123).
  * Stacktrace recovery machinery improved: cycle detection works through recovered exceptions, cancellation exceptions are recovered on cancellation fast-path.
  * Atomicfu-related bug fixes: publish transformed artifacts, do not propagate transitive atomicfu dependency (#1064, #1116).
  * Publication to NPM fixed (#1118).
  * Misplaced resources are removed from the final jar (#1131).

## Version 1.2.0

 * Kotlin updated to 1.3.30.
 * New API: `CancellableContinuation.resume` with `onCancelling` lambda (#1044) to consistently handle closeable resources.
 * Play services task version updated to 16.0.1.
 * `ReceiveChannel.isEmpty` is no longer deprecated

A lot of `Flow` improvements:
  * Purity property is renamed to context preservation and became more restrictive.
  * `zip` and `combineLatest` operators.
  * Integration with RxJava2
  * `flatMap`, `merge` and `concatenate` are replaced with `flattenConcat`, `flattenMerge`, `flatMapConcat` and `flatMapMerge`.
  * Various documentation improvements and minor bug fixes.
  
Note that `Flow` **is not** leaving its [preview status](/docs/topics/compatibility.md#flow-preview-api).
  
## Version 1.2.0-alpha-2

This release contains major [feature preview](/docs/topics/compatibility.md#flow-preview-api): cold streams aka `Flow` (#254). 

Performance:
* Performance of `Dispatcher.Main` initialization is significantly improved (#878).

## Version 1.2.0-alpha

* Major debug agent improvements. Real stacktraces are merged with coroutine stacktraces for running coroutines, merging heuristic is improved, API is cleaned up and is on its road to stabilization (#997).
* `CoroutineTimeout` rule or JUnit4 is introduced to simplify coroutines debugging (#938).
* Stacktrace recovery improvements. Exceptions with custom properties are no longer copied, `CopyableThrowable` interface is introduced, machinery is [documented](https://github.com/Kotlin/kotlinx.coroutines/blob/develop/docs/debugging.md) (#921, #950).
* `Dispatchers.Unconfined`, `MainCoroutineDispatcher.immediate`, `MainScope` and `CoroutineScope.cancel` are promoted to stable API (#972).
* `CompletableJob` is introduced (#971).
* Structured concurrency is integrated into futures and listenable futures (#1008).
* `ensurePresent` and `isPresent` extensions for `ThreadLocal` (#1028).
* `ensureActive` extensions for `CoroutineContext`, `CoroutineScope` and `Job` (#963).
* `SendChannel.isFull` and `ReceiveChannel.isEmpty` are deprecated (#1053).
* `withContext` checks cancellation on entering (#962).
* Operator `invoke` on `CoroutineDispatcher` (#428).
* Java 8 extensions for `delay` and `withTimeout` now properly handle too large values (#428).
* A global exception handler for fatal exceptions in coroutines is introduced (#808, #773).
* Major improvements in cancellation machinery and exceptions delivery consistency. Cancel with custom exception is completely removed.
* Kotlin version is updated to 1.3.21.
* Do not use private API on newer Androids to handle exceptions (#822).

Bug fixes:
* Proper `select` support in debug agent (#931).
* Proper `supervisorScope` support in debug agent (#915).
* Throwing `initCause` does no longer trigger an internal error (#933).
* Lazy actors are started when calling `close` in order to cleanup their resources (#939).
* Minor bugs in reactive integrations are fixed (#1008).
* Experimental scheduler shutdown sequence is fixed (#990).

## Version 1.1.1

* Maintenance release, no changes in the codebase
* Kotlin is updated to 1.3.20
* Gradle is updated to 4.10
* Native module is published with Gradle metadata v0.4 

## Version 1.1.0

* Kotlin version updated to 1.3.11.
* Resumes to `CancellableContinuation` in the final state produce `IllegalStateException` (#901). This change does not affect #830, races between resume and cancellation do not lead to an exceptional situation.
* `runBlocking` is integrated with `Dispatchers.Unconfined` by sharing an internal event loop. This change does not affect the semantics of the previously correct code but allows to mix multiple `runBlocking` and unconfined tasks (#860).

## Version 1.1.0-alpha

### Major improvements in coroutines testing and debugging
* New module: [`kotlinx-coroutines-debug`](https://github.com/Kotlin/kotlinx.coroutines/blob/master/core/kotlinx-coroutines-debug/README.md). Debug agent that improves coroutines stacktraces, allows to print all active coroutines and its hierarchies and can be installed as Java agent.
* New module: [`kotlinx-coroutines-test`](https://github.com/Kotlin/kotlinx.coroutines/blob/master/core/kotlinx-coroutines-test/README.md). Allows setting arbitrary `Dispatchers.Main` implementation for tests (#810).
* Stacktrace recovery mechanism. Exceptions from coroutines are recovered from current coroutine stacktraces to simplify exception diagnostic. Enabled in debug mode, controlled by `kotlinx.coroutines.debug` system property (#493).

### Other improvements
* `MainScope` factory and `CoroutineScope.cancel` extension (#829). One line `CoroutineScope` integration!
* `CancellableContinuation` race between `resumeWithException` and `cancel` is addressed, exceptions during cancellation are no longer reported to exception handler (#830, #892).
* `Dispatchers.Default` now consumes much less CPU on JVM (#840).
* Better diagnostic and fast failure if an uninitialized dispatcher is used (#880).
* Conflated channel becomes linearizable.
* Fixed inconsistent coroutines state when the result of the coroutine had type `DisposableHandle` (#835).
* Fixed `JavaFx` initialization bug (#816).
* `TimeoutCancellationException` is thrown by `withTimeout` instead of `CancellationException` if negative timeout is supplied (#870).
* Kotlin/Native single-threaded workers support: coroutines can be safely used in multiple independent K/N workers.
* jsdom support in `Dispatchers.Default` on JS.
* rxFlowable generic parameter is now restricted with Any.
* Guava 27 support in `kotlinx-coroutines-guava`.
* Coroutines are now built with progressive mode.
* Various fixes in the documentation.

## Version 1.0.1
 
* Align `publisher` implementation with Reactive TCK.
* Reimplement `future` coroutine builders on top of `AbstractCoroutine`	(#751).
* Performance optimizations in `Dispatchers.Default` and `Dispatchers.IO`.
* Use only public API during `JavaFx` instantiation, fixes warnings on Java 9 and build on Java 11 (#463).
* Updated contract of `CancellableContinuation.resumeWithException` (documentation fix, see #712).
* Check cancellation on fast-path of all in-place coroutine builders (`withContext`, `coroutineScope`, `supervisorScope`, `withTimeout` and `withTimeoutOrNull`).
* Add optional prefix to thread names of `ExperimentalCoroutineDispatcher` (#661).
* Fixed bug when `ExperimentalCoroutineDispatcher` could end up in inconsistent state if `Thread` constructor throws an exception (#748).

## Version 1.0.0

* All Kotlin dependencies updated to 1.3 release version.
* Fixed potential memory leak in `HandlerDispatcher.scheduleResumeAfterDelay`, thanks @cbeyls.
* `yield` support for `Unconfined` and immediate dispatchers (#737).
* Various documentation improvements.

## Version 1.0.0-RC1

* Coroutines API is updated to Kotlin 1.3.
* Deprecated API is removed or marked as `internal`.
* Experimental and internal coroutine API is marked with corresponding `kotlin.experimental.Experimental` annotation. If you are using `@ExperimentalCoroutinesApi` or `@InternalCoroutinesApi` you should explicitly opt-in, otherwise compilation warning (or error) will be produced. 
* `Unconfined` dispatcher (and all dispatchers which support immediate invocation) forms event-loop on top of current thread, thus preventing all `StackOverflowError`s. `Unconfined` dispatcher is now much safer for the general use and may leave its experimental status soon (#704).
* Significantly improved performance of suspending hot loops in `kotlinx.coroutines` (#537).
* Proguard rules are embedded into coroutines JAR to assist jettifier (#657)
* Fixed bug in shutdown sequence of `runBlocking` (#692).
* `ReceiveChannel.receiveOrNull` is marked as obsolete and deprecated.
* `Job.cancel(cause)` and `ReceiveChannel.cancel(cause)` are deprecated, `cancel()` returns `Unit` (#713).

## Version 0.30.2

* `Dispatchers.Main` is instantiated lazily (see #658 and #665).
* Blocking coroutine dispatcher views are now shutdown properly (#678).
* Prevent leaking Kotlin 1.3 from atomicfu dependency (#659).
* Thread-pool based dispatcher factories are marked as obsolete (#261).
* Fixed exception loss on `withContext` cancellation (#675).   

## Version 0.30.1

Maintenance release:
* Added `Dispatchers.Main` to common dispatchers, which can be used from Android, Swing and JavaFx projects if a corresponding integration library is added to dependencies. 
* With `Dispatchers.Main` improvement tooling bug in Android Studio #626 is mitigated, so Android users now can safely start the migration to the latest `kotlinx.coroutines` version.
* Fixed bug with thread unsafety of shutdown sequence in `EventLoop`.
* Experimental coroutine dispatcher now has `close` contract similar to Java `Executor`, so it can be safely instantiated and closed multiple times (affects only unit tests).
* Atomicfu version is updated with fixes in JS transformer (see #609)

## Version 0.30.0

* **[Major]** Further improvements in exception handling &mdash; no failure exception is lost. 
  * `async` and async-like builders cancel parent on failure (it affects `CompletableDeferred`, and all reactive integration builders).
  * This makes parallel decomposition exception-safe and reliable without having to rember about `awaitAll` (see #552).
  * `Job()` wih parent now also cancels parent on failure consistently with other scopes.
  * All coroutine builders and `Job` implementations propagate failure to the parent unless it is a `CancellationException`. 
  * Note, "scoping" builders don't "cancel the parent" verbatim, but rethrow the corresponding exception to the caller for handling.
  * `SupervisorJob()` and `supervisorScope { ... }` are introduced, allowing for a flexible implementation of custom exception-handling policies, see a [new section in the guide on supervision](docs/topics/exception-handling.md#supervision).
  * Got rid of `awaitAll` in documentation and rewrote `currentScope` section (see #624).
* **[Major]** Coroutine scheduler is used for `Dispatchers.Default` by default instead of deprecated `CommonPool`.
  * "`DefaultDispatcher`" is used as a public name of the default impl (you'll see it thread names and in the guide).
  * `-Dkotlinx.coroutines.scheduler=off` can be used to switch back to `CommonPool` for a time being (until deprecated CommonPool is removed).  
* Make `CoroutineStart.ATOMIC` experimental as it covers important use-case with resource cleanup in finally block (see #627).
* Restored binary compatibility of `Executor.asCoroutineDispatcher` (see #629).
* Fixed OOM in thread-pool dispatchers (see #571).
* Check for cancellation when starting coroutine with `Dispatchers.Unconfined` (see #621).
* A bunch of various performance optimizations and docs fixes, including contributions from @AlexanderPrendota, @PaulWoitaschek.

## Version 0.27.0 

* **[Major]** Public API revision. All public API was reviewed and marked as preparation to `1.0` release:
   1. `@Deprecated` API. All API marked as deprecated will be removed in 1.0 release without replacement.
   2. `@ExperimentalCoroutinesApi` API. This API is experimental and may change in the future, but migration mechanisms will be provided. Signature, binary compatibility and semantics can be changed.
   3. `@InternalCoroutinesApi`. This API is intended to be used **only** from within `kotlinx.coroutines`. It can and will be changed, broken 
       and removed in the future releases without any warnings and migration aids. If you find yourself using this API, it is better to report
       your use-case to Github issues, so decent, stable and well-tested alternative can be provided.
   4. `@ObsoleteCoroutinesApi`. This API has serious known flaws and will be replaced with a better alternative in the nearest releases.
   5. Regular public API. This API is proven to be stable and is not going to be changed. If at some point it will be discovered that such API
      has unfixable design flaws, it will be gradually deprecated with proper replacement and migration aid, but won't be removed for at least a year.
* **[Major]** Job state machine is reworked. It includes various performance improvements, fixes in 
data-races which could appear in a rare circumstances and consolidation of cancellation and exception handling.
Visible consequences of include more robust exception handling for large coroutines hierarchies and for different kinds of `CancellationException`, transparent parallel decomposition and consistent view of coroutines hierarchy in terms of its state (see #220 and #585).
* NIO, Quasar and Rx1 integration modules are removed with no replacement (see #595, #601, #603).
* `withContext` is now aligned with structured concurrency and awaits for all launched tasks, its performance is significantly improved (see #553 and #617).
* Added integration module with Play Services Task API. Thanks @SUPERCILEX and @lucasvalenteds for the contribution!
* Integration with Rx2 now respects nullability in type constraints (see #347). Thanks @Dmitry-Borodin for the contribution!
* `CompletableFuture.await` and `ListenableFuture.await` now propagate cancellation to the future (see #611).
* Cancellation of `runBlocking` machinery is improved (see #589).
* Coroutine guide is restructured and split to multiple files for the sake of simplicity.
* `CoroutineScope` factory methods add `Job` if it is missing from the context to enforce structured concurrency (see #610).
* `Handler.asCoroutineDispatcher` has a `name` parameter for better debugging (see #615).
* Fixed bug when `CoroutineSchedule` was closed from one of its threads (see #612).
* Exceptions from `CoroutineExceptionHandler` are reported by default exception handler (see #562).
* `CoroutineName` is now available from common modules (see #570).
* Update to Kotlin 1.2.70.

## Version 0.26.1

* Android `Main` dispatcher is `async` by default which may significantly improve UI performance. Contributed by @JakeWharton (see #427).
* Fixed bug when lazily-started coroutine with registered cancellation handler was concurrently started and cancelled. 
* Improved termination sequence in IO dispatcher.
* Fixed bug with `CoroutineScope.plus` operator (see #559).
* Various fixes in the documentation. Thanks to @SUPERCILEX, @yorlov, @dualscyther and @soudmaijer!

## Version 0.26.0

* Major rework of `kotlinx.coroutines` concurrency model (see #410 for a full explanation of the rationale behind this change):
  * All coroutine builders are now extensions on `CoroutineScope` and inherit its `coroutineContext`. Standalone builders are deprecated.
  * As a consequence, all nested coroutines launched via builders now automatically establish parent-child relationship and inherit `CoroutineDispatcher`.
  * All coroutine builders use `Dispatchers.Default` by default if `CoroutineInterceptor` is not present in their context.
  * [CoroutineScope](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/) became the first-class citizen in `kolinx.coroutines`.
  * `withContext` `block` argument has `CoroutineScope` as a receiver.
  * [GlobalScope](https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-global-scope/) is introduced to simplify migration to new API and to launch global-level coroutines.
  * `currentScope` and `coroutineScope` builders are introduced to extract and provide `CoroutineScope`.
  * Factory methods to create `CoroutineScope` from `CoroutineContext` are introduced.
  * `CoroutineScope.isActive` became an extension property.
  * New sections about structured concurrency in core guide: ["Structured concurrency"](docs/topics/coroutines-guide.md#structured-concurrency), ["Scope builder"](docs/topics/coroutines-guide.md#scope-builder) and ["Structured concurrency with async"](docs/topics/coroutines-guide.md#structured-concurrency-with-async).
  * New section in UI guide with Android example: ["Structured concurrency, lifecycle and coroutine parent-child hierarchy"](ui/coroutines-guide-ui.md#structured-concurrency,-lifecycle-and-coroutine-parent-child-hierarchy).
  * Deprecated reactive API is removed.
* Dispatchers are renamed and grouped in the Dispatchers object (see #41 and #533):
  * Dispatcher names are consistent.
  * Old dispatchers including `CommonPool` are deprecated.
* Fixed bug with JS error in rare cases in `invokeOnCompletion(onCancelling = true)`.
* Fixed loading of Android exception handler when `Thread.contextClassLoader` is mocked (see #530).
* Fixed bug when `IO` dispatcher silently hung (see #524 and #525) .

## Version 0.25.3

* Distribution no longer uses multi-version jar which is not supported on Android (see #510).
* JS version of the library does not depend on AtomicFu anymore:
  All the atomic boxes in JS are fully erased.
* Note that versions 0.25.1-2 are skipped for technical reasons (they were not fully released).

## Version 0.25.0

* Major rework on exception-handling and cancellation in coroutines (see #333, #452 and #451):
  * New ["Exception Handling" section in the guide](docs/topics/coroutines-guide.md#exception-handling) explains exceptions in coroutines. 
  * Semantics of `Job.cancel` resulting `Boolean` value changed &mdash; `true` means exception was handled by the job, caller shall handle otherwise.
  * Exceptions are properly propagated from children to parents.
  * Installed `CoroutineExceptionHandler` for a family of coroutines receives one aggregated exception in case of failure.
  * Change `handleCoroutineException` contract, so custom exception handlers can't break coroutines machinery. 
  * Unwrap `JobCancellationException` properly to provide exception transparency over whole call chain.
* Introduced support for thread-local elements in coroutines context (see #119):
  * `ThreadContextElement` API for custom thread-context sensitive context elements.
  * `ThreadLocal.asContextElement()` extension function to convert an arbitrary thread-local into coroutine context element.
  * New ["Thread-local data" subsection in the guide](docs/topics/coroutines-guide.md#thread-local-data) with examples.
  * SLF4J Mapped Diagnostic Context (MDC) integration is provided via `MDCContext` element defined in [`kotlinx-coroutines-slf4j`](integration/kotlinx-coroutines-slf4j/README.md) integration module.
* Introduced IO dispatcher to offload blocking I/O-intensive tasks (see #79).
* Introduced `ExecutorCoroutineDispatcher` instead of `CloseableCoroutineDispatcher` (see #385). 
* Built with Kotlin 1.2.61 and Kotlin/Native 0.8.2.
* JAR files for `kotlinx-coroutines` are now [JEP 238](https://openjdk.java.net/jeps/238) multi-release JAR files.
  * On JDK9+ `VarHandle` is used for atomic operations instead of `Atomic*FieldUpdater` for better performance.
  * See [AtomicFu](https://github.com/Kotlin/kotlinx.atomicfu/blob/master/README.md) project for details.
* Reversed addition of `BlockingChecker` extension point to control where `runBlocking` can be used (see #227).
  * `runBlocking` can be used anywhere without limitations (again), but it would still cause problems if improperly used on UI thread.
* Corrected return-type of `EventLoop` pseudo-constructor (see #477, PR by @Groostav).  
* Fixed `as*Future()` integration functions to catch all `Throwable` exceptions (see #469).
* Fixed `runBlocking` cancellation (see #501).
* Fixed races and timing bugs in `withTimeoutOrNull` (see #498).
* Execute `EventLoop.invokeOnTimeout` in `DefaultDispatcher` to allow busy-wait loops inside `runBlocking` (see #479).
* Removed `kotlinx-coroutines-io` module from the project, it has moved to [kotlinx-io](https://github.com/kotlin/kotlinx-io/).
* Provide experimental API to create limited view of experimental dispatcher (see #475). 
* Various minor fixes by @LouisCAD, @Dmitry-Borodin.

## Version 0.24.0

* Fully multiplatform release with Kotlin/Native support (see #246):
  * Only single-threaded operation inside `runBlocking` event loop is supported at this moment.
  * See details on setting up build environment [here](native/README.md). 
* Improved channels:
  * Introduced `SendChannel.invokeOnClose` (see #341).
  * Make `close`, `cancel`, `isClosedForSend`, `isClosedForReceive` and `offer` linearizable with other operations (see #359).
  * Fixed bug when send operation can be stuck in channel forever.
  * Fixed broadcast channels on JS (see #412).
* Provides `BlockingChecker` mechanism which checks current context (see #227).
  * Attempts to use `runBlocking` from any supported UI thread (Android, JavaFx, Swing) will result in exception.
* Android: 
  * Worked around Android bugs with zero-size ForkJoinPool initialization (see #432, #288).
  * Introduced `UI.immediate` extension as performance-optimization to immediately execute tasks which are invoked from the UI thread  (see #381). 
    * Use it only when absolutely needed. It breaks asynchrony of coroutines and may lead to surprising and unexpected results.
* Fixed materialization of a `cause` exception for `Job` onCancelling handlers (see #436).  
* Fixed JavaFx `UI` on Java 9 (see #443).
* Fixed and documented the order between cancellation handlers and continuation resume (see #415).
* Fixed resumption of cancelled continuation (see #450).
* Includes multiple fixes to documentation contributed by @paolop, @SahilLone, @rocketraman, @bdavisx, @mtopolnik, @Groostav.   
* Experimental coroutines scheduler preview (JVM only):
  * Written from scratch and optimized for communicating coroutines.
  * Performs significantly better than ForkJoinPool on coroutine benchmarks and for connected applications with [ktor](https://ktor.io).
  * Supports automatic creating of new threads for blocking operations running on the same thread pool (with an eye on solving #79), but there is no stable public API for it just yet.
  * For preview, run JVM with `-Dkotlinx.coroutines.scheduler` option. In this case `DefaultDispatcher` is set to new experimental scheduler instead of FJP-based `CommonPool`.
  * Submit your feedback to issue #261.

## Version 0.23.4

* Recompiled with Kotlin 1.2.51 to solve broken metadata problem (see [KT-24944](https://youtrack.jetbrains.com/issue/KT-24944)).

## Version 0.23.3

* Kotlin 1.2.50.
* JS: Moved to atomicfu version 0.10.3 that properly matches NPM & Kotlin/JS module names (see #396).
* Improve source-code compatibility with previous (0.22.x) version of `openChannel().use { ... }` pattern by providing deprecated extension function `use` on `ReceiveChannel`.

## Version 0.23.2

* IO: fix joining and continuous writing byte array interference.

## Version 0.23.1

* JS: Fix dependencies in NPM: add "kotlinx-atomicfu" dependency (see #370).
* Introduce `broadcast` coroutine builder (see #280):
  * Support `BroadcastChannel.cancel` method to drop the buffer.
  * Introduce `ReceiveChannel.broadcast()` extension. 
* Fixed a bunch of doc typos (PRs by @paolop).
* Corrected previous version's release notes (PR by @ansman).  

## Version 0.23.0

* Kotlin 1.2.41
* **Coroutines core module is made mostly cross-platform for JVM and JS**:
  * Migrate channels and related operators to common, so channels can be used from JS (see #201).
  * Most of the code is shared between JVM and JS versions using cross-platform version of [AtomicFU](https://github.com/Kotlin/kotlinx.atomicfu) library.
  * The recent version of Kotlin allows default parameters in common code (see #348).
  * The project is built using Gradle 4.6. 
* **Breaking change**: `CancellableContinuation` is not a `Job` anymore (see #219):
  * It does not affect casual users of `suspendCancellableCoroutine`, since all the typically used functions are still there.
  * `CancellableContinuation.invokeOnCompletion` is deprecated now and its semantics had subtly changed:
     * `invokeOnCancellation` is a replacement for `invokeOnCompletion` to install a handler.
     * The handler is **not** invoked on `resume` which corresponds to the typical usage pattern.
     * There is no need to check for `cont.isCancelled` in a typical handler code anymore (since handler is invoked only when continuation is cancelled). 
     * Multiple cancellation handlers cannot be installed.
     * Cancellation handlers cannot be removed (disposed of) anymore.  
  * This change is designed to allow better performance of suspending cancellable functions: 
     * Now `CancellableContinuation` implementation has simpler state machine and is implemented more efficiently. 
  * Exception handling in `AbstractContinuation` (that implements `CancellableContinuation`) is now consistent: 
     * Always prefer exception thrown from coroutine as exceptional reason, add cancellation cause as suppressed exception.      
* **Big change**: Deprecate `CoroutineScope.coroutineContext`:
  * It is replaced with top-level `coroutineContext` function from Kotlin standard library.
* Improve `ReceiveChannel` operators implementations to guarantee closing of the source channels under all circumstances (see #279):
  * `onCompletion` parameter added to `produce` and all other coroutine builders.
  * Introduce `ReceiveChannel.consumes(): CompletionHandler` extension function.
* Replace `SubscriptionReceiveChannel` with `ReceiveChannel` (see #283, PR by @deva666).
  * `ReceiveChannel.use` extension is introduced to preserve source compatibility, but is deprecated.
    * `consume` or `consumeEach` extensions should be used for channels.
    * When writing operators, `produce(onCompletion=consumes())  { ... }` pattern shall be used (see #279 above). 
* JS: Kotlin is declared as peer dependency (see #339, #340, PR by @ansman).  
* Invoke exception handler for actor on cancellation even when channel was successfully closed, so exceptions thrown by actor are always reported (see #368).
* Introduce `awaitAll` and `joinAll` for `Deferred` and `Job` lists correspondingly (see #171).  
* Unwrap `CompletionException` exception in `CompletionStage.await` slow-path to provide consistent results (see #375).
* Add extension to `ExecutorService` to return `CloseableCoroutineDispatcher` (see #278, PR by @deva666).
* Fail with proper message during build if JDK_16 is not set (see #291, PR by @venkatperi).
* Allow negative timeouts in `delay`, `withTimeout` and `onTimeout` (see #310).
* Fix a few bugs (leaks on cancellation) in `delay`:
  * Invoke `clearTimeout` on cancellation in JSDispatcher.
  * Remove delayed task on cancellation from internal data structure on JVM.
* Introduce `ticker` function to create "ticker channels" (see #327):
  * It provides analogue of RX `Observable.timer` for coroutine channels.
  * It is currently supported on JVM only.
* Add a test-helper class `TestCoroutineContext` (see #297, PR by @streetsofboston).  
  * It is currently supported on JVM only.
  * Ticker channels (#327) are not yet compatible with it. 
* Implement a better way to set `CoroutineContext.DEBUG` value (see #316, PR by @dmytrodanylyk):
  * Made `CoroutineContext.DEBUG_PROPERTY_NAME` constant public.
  * Introduce public constants with `"on"`, `"off"`, `"auto"` values.
* Introduce system property to control `CommonPool` parallelism (see #343):
  * `CommonPool.DEFAULT_PARALLELISM_PROPERTY_NAME` constant is introduced with a value of "kotlinx.coroutines.default.parallelism".
* Include package-list files into documentation site (see #290).
* Fix various typos in docs (PRs by @paolop and @ArtsiomCh).  

## Version 0.22.5

* JS: Fixed main file reference in [NPM package](https://www.npmjs.com/package/kotlinx-coroutines-core)
* Added context argument to `Channel.filterNot` (PR by @jcornaz).
* Implemented debug `toString` for channels (see #185).

## Version 0.22.4

* JS: Publish to NPM (see #229).
* JS: Use node-style dispatcher on ReactNative (see #236).
* [jdk8 integration](integration/kotlinx-coroutines-jdk8/README.md) improvements: 
  * Added conversion from `CompletionStage` to `Deferred` (see #262, PR by @jcornaz).
  * Use fast path in `CompletionStage.await` and make it cancellable.

## Version 0.22.3

* Fixed `produce` builder to close the channel on completion instead of cancelling it, which lead to lost elements with buffered channels (see #256).
* Don't use `ForkJoinPool` if there is a `SecurityManager` present to work around JNLP problems (see #216, PR by @NikolayMetchev). 
* JS: Check for undefined `window.addEventListener` when choosing default coroutine dispatcher (see #230, PR by @ScottPierce).
* Update 3rd party dependencies:
  * [kotlinx-coroutines-rx1](reactive/kotlinx-coroutines-rx1) to RxJava version `1.3.6`.
  * [kotlinx-coroutines-rx2](reactive/kotlinx-coroutines-rx2) to RxJava version `2.1.9`.
  * [kotlinx-coroutines-guava](integration/kotlinx-coroutines-guava) to Guava version `24.0-jre`.
  
## Version 0.22.2

* Android: Use @Keep annotation on AndroidExceptionPreHandler to fix the problem on Android with minification enabled (see #214).
* Reactive: Added `awaitFirstOrDefault` and `awaitFirstOrNull` extensions (see #224, PR by @konrad-kaminski).
* Core: Fixed `withTimeout` and `withTimeoutOrNull` that should not use equals on result (see #212, PR by @konrad-kaminski).
* Core: Fixed hanged receive from a closed subscription of BroadcastChannel (see #226).
* IO: fixed error propagation (see https://github.com/ktorio/ktor/issues/301).
* Include common sources into sources jar file to work around KT-20971.
* Fixed bugs in documentation due to MPP.

## Version 0.22.1

* Migrated to Kotlin 1.2.21.
* Improved `actor` builder documentation (see #210) and fixed bugs in rendered documentation due to multiplatform.
* Fixed `runBlocking` to properly support specified dispatchers (see #209).
* Fixed data race in `Job` implementation (it was hanging at `LockFreeLinkedList.helpDelete` on certain stress tests).
* `AbstractCoroutine.onCancellation` is invoked before cancellation handler that is set via `invokeOnCompletion`.
* Ensure that `launch` handles uncaught exception before another coroutine that uses `join` on it resumes (see #208).

## Version 0.22

* Migrated to Kotlin 1.2.20.
* Introduced stable public API for `AbstractCoroutine`:
  * Implements `Job`, `Continuation`, and `CoroutineScope`.
  * Has overridable `onStart`, `onCancellation`, `onCompleted` and `onCompletedExceptionally` functions.
  * Reactive integration modules are now implemented using public API only.
  * Notifies onXXX before all the installed handlers, so `launch` handles uncaught exceptions before "joining" coroutines wakeup (see #208).

## Version 0.21.2

* Fixed `openSubscription` extension for reactive `Publisher`/`Observable`/`Flowable` when used with `select { ... }` and added an optional `request` parameter to specify how many elements are requested from publisher in advance on subscription (see #197).
* Simplified implementation of `Channel.flatMap` using `toChannel` function to work around Android 5.0 APK install SIGSEGV (see #205).

## Version 0.21.1

* Improved performance of coroutine dispatching (`DispatchTask` instance is no longer allocated).
* Fixed `Job.cancel` and `CompletableDeferred.complete` to support cancelling/completing states and properly wait for their children to complete on join/await (see #199).
* Fixed a bug in binary heap implementation (used internally by `delay`) which could have resulted in wrong delay time in rare circumstances.
* Coroutines library for [Kotlin/JS](js/README.md):
  * `Promise.asDeferred` immediately installs handlers to avoid "Unhandled promise rejection" warning.
  * Use `window.postMessage` instead of `setTimeout` for coroutines inside the browser to avoid timeout throttling (see #194).
  * Use custom queue in `Window.awaitAnimationFrame` to align all animations and reduce overhead.
  * Introduced `Window.asCoroutineDispatcher()` extension function.

## Version 0.21

* Migrated to Kotlin 1.2.10.
* Coroutines library for [Kotlin/JS](js/README.md) and [multiplatform projects](https://kotlinlang.org/docs/reference/multiplatform.html) (see #33):
  * `launch` and `async` coroutine builders.
  * `Job` and `Deferred` light-weight future with cancellation support.
  * `delay` and `yield` top-level suspending functions.
  * `await` extension for JS `Promise` and `asPromise`/`asDeferred` conversions.
  * `promise` coroutine builder.
  * `Job()` and `CompletableDeferred()` factories.
  * Full support for parent-child coroutine hierarchies.
  * `Window.awaitAnimationFrame` extension function.
  * [Sample frontend Kotlin/JS application](js/example-frontend-js/README.md) with coroutine-driven animations.
* `run` is deprecated and renamed to `withContext` (see #134).
* `runBlocking` and `EventLoop` implementations optimized (see #190).

## Version 0.20

* Migrated to Kotlin 1.2.0.
* Channels:
  * Sequence-like `filter`, `map`, etc extensions on `ReceiveChannel` are introduced (see #88 by @fvasco and #69 by @konrad-kaminski).
  * Introduced `ReceiveChannel.cancel` method.
  * All operators on `ReceiveChannel` fully consume the original channel (`cancel` it when they are done) using a helper `consume` extension.
  * Deprecated `ActorJob` and `ProducerJob`; `actor` now returns `SendChannel` and `produce` returns `ReceiveChannel` (see #127).
  * `SendChannel.sendBlocking` extension method (see #157 by @@fvasco).
* Parent-child relations between coroutines:
  * Introduced an optional `parent` job parameter for all coroutine builders so that code with an explict parent `Job` is more natural.
  * Added `parent` parameter to `CompletableDeferred` constructor.
  * Introduced `Job.children` property.
  * `Job.cancelChildren` is now an extension (member is deprecated and hidden).
  * `Job.joinChildren` extension is introduced.
  * Deprecated `Job.attachChild` as a error-prone API.
  * Fixed StackOverflow when waiting for a lot of completed children that did not remove their handlers from the parent.
* Use `java.util.ServiceLoader` to find default instances of `CoroutineExceptionHandler`.
* Android UI integration:
  * Use `Thread.getUncaughtExceptionPreHandler` to make sure that exceptions are logged before crash (see #148).
  * Introduce `UI.awaitFrame` for animation; added sample coroutine-based animation application for Android [here](ui/kotlinx-coroutines-android/animation-app).
  * Fixed `delay(Long.MAX_VALUE)` (see #161)  
* Added missing `DefaultDispatcher` on some reactive operators (see #174 by @fvasco)
* Fixed `actor` and `produce` so that a cancellation of a Job cancels the underlying channel (closes and removes all the pending messages).  
* Fixed sporadic failure of `example-context-06` (see #160)
* Fixed hang of `Job.start` on lazy coroutine with attached `invokeOnCompletion` handler.
* A more gradual introduction to `runBlocking` and coroutines in the [guide](docs/topics/coroutines-guide.md) (see #166).

## Version 0.19.3

* Fixed `send`/`openSubscription` race in `ArrayBroadcastChannel`.
  This race lead to stalled (hanged) `send`/`receive` invocations.
* Project build has been migrated to Gradle.  

## Version 0.19.2

* Fixed `ArrayBroadcastChannel` receive of stale elements on `openSubscription`. 
  Only elements that are sent after invocation of `openSubscription` are received now.
* Added a default value for `context` parameter to `rxFlowable` (see #146 by @PhilGlass).
* Exception propagation logic from cancelled coroutines is adjusted (see #152):
  * When cancelled coroutine crashes due to some other exception, this other exception becomes the cancellation reason 
    of the coroutine, while the original cancellation reason is suppressed.
  * `UnexpectedCoroutineException` is no longer used to report those cases as is removed.
  * This fixes a race between crash of CPU-consuming coroutine and cancellation which resulted in an unhandled exception 
    and lead to crashes on Android.
* `run` uses cancelling state & propagates exceptions when cancelled (see #147):
  * When coroutine that was switched into a different dispatcher using `run` is cancelled, the run invocation does not 
    complete immediately, but waits until the body completes.
  * If the body completes with exception, then this exception is propagated.
* No `Job` in `newSingleThreadContext` and `newFixedThreadPoolContext` anymore (see #149, #151):
  * This resolves the common issue of using `run(ctx)` where ctx comes from either `newSingleThreadContext` or 
    `newFixedThreadPoolContext` invocation. They both used to return a combination of dispatcher + job,
     and this job was overriding the parent job, thus preventing propagation of cancellation. Not anymore.
  * `ThreadPoolDispatcher` class is now public and is the result type for both functions. 
     It has the `close` method to release the thread pool.

## Version 0.19.1

* Failed parent Job cancels all children jobs, then waits for them them.
  This makes parent-child hierarchies easier to get working right without
  having to use `try/catch` or other exception handlers.  
* Fixed a race in `ArrayBroadcastChannel` between `send` and `openChannel` invocations
  (see #138).   
* Fixed quite a rare race in `runBlocking` that resulted in `AssertionError`. 
  Unfortunately, cannot write a reliable stress-test to reproduce it. 
* Updated Reactor support to leverage Bismuth release train 
  (contributed by @sdeleuze, see PR #141)

## Version 0.19

* This release is published to Maven Central.
* `DefaultDispatcher` is introduced (see #136):
  * `launch`, `async`, `produce`, `actor` and other integration-specific coroutine builders now use 
    `DefaultDispatcher` as the default value for their `context` parameter.
  * When a context is explicitly specified, `newCoroutineContext` function checks if there is any
    interceptor/dispatcher defined in the context and uses `DefaultDispatcher` if there is none.  
  * `DefaultDispatcher` is currently defined to be equal to `CommonPool`.     
  * Examples in the [guide](docs/topics/coroutines-guide.md) now start with `launch { ... }` code and explanation on the nature
    and the need for coroutine context starts in "Coroutine context and dispatchers" section.  
* Parent coroutines now wait for their children (see #125):
  * Job _completing_ state is introduced in documentation as a state in which parent coroutine waits for its children.
  * `Job.attachChild` and `Job.cancelChildren` are introduced.
  * `Job.join` now always checks cancellation status of invoker coroutine for predictable behavior when joining
     failed child coroutine. 
  * `Job.cancelAndJoin` extension is introduced.    
  * `CoroutineContext.cancel` and `CoroutineContext.cancelChildren` extensions are introduced for convenience. 
  * `withTimeout`/`withTimeoutOrNull` blocks become proper coroutines that have `CoroutineScope` and wait for children, too.
  * Diagnostics in cancellation and unexpected exception messages are improved, 
    coroutine name is included in debug mode.
  * Fixed cancellable suspending functions to throw `CancellationException` (as was documented before) even when 
    the coroutine is cancelled with another application-specific exception.
  * `JobCancellationException` is introduced as a specific subclass of `CancellationException` which is 
    used for coroutines that are cancelled without cause and to wrap application-specific exceptions.   
  * `Job.getCompletionException` is renamed to `Job.getCancellationException` and return a wrapper exception if needed.
  * Introduced `Deferred.getCompletionExceptionOrNull` to get not-wrapped exception result of `async` task.
  * Updated docs for `Job` & `Deferred` to explain parent/child relations.
* `select` expression is modularized:
  * `SelectClause(0,1,2)` interfaces are introduced, so that synchronization
    constructs can define their select clauses without having to modify
    the source of the `SelectBuilder` in `kotlinx-corounes-core` module.
  * `Job.onJoin`, `Deferred.onAwait`, `Mutex.onLock`, `SendChannel.onSend`, `ReceiveChannel.onReceive`, etc
    that were functions before are now properties returning the corresponding select clauses. Old functions
    are left in bytecode for backwards compatibility on use-site, but any outside code that was implementing those 
    interfaces by itself must be updated.  
  * This opens road to moving channels into a separate module in future updates.
* Renamed `TimeoutException` to `TimeoutCancellationException` (old name is deprecated).  
* Fixed various minor problems:    
  * JavaFx toolkit is now initialized by `JavaFx` context (see #108).
  * Fixed lost ACC_STATIC on <clinit> methods (see #116).
  * Fixed link to source code from documentation (see #129).
  * Fixed `delay` in arbitrary contexts (see #133).
* `kotlinx-coroutines-io` module is introduced. It is a work-in-progress on `ByteReadChannel` and `ByteWriteChannel`
   interfaces, their implementations, and related classes to enable convenient coroutine integration with various 
   asynchronous I/O libraries and sockets. It is currently _unstable_ and **will change** in the next release.  

## Version 0.18

* Kotlin 1.1.4 is required to use this version, which enables:
  * `withLock` and `consumeEach` functions are now inline suspend functions.
  * `JobSupport` class implementation is optimized (one fewer field).
* `TimeoutException` is public (see #89).
* Improvements to `Mutex` (courtesy of @fvasco):
  * Introduced `holdsLock` (see #92).
  * Improved documentation on `Mutex` fairness (see #90).
* Fixed NPE when `ArrayBroadcastChannel` is closed concurrently with receive (see #97).
* Fixed bug in internal class LockFreeLinkedList that resulted in ISE under stress in extremely rare circumstances.
* Integrations:
  * [quasar](integration/kotlinx-coroutines-quasar): Introduced integration with suspendable JVM functions
    that are instrumented with [Parallel Universe Quasar](https://docs.paralleluniverse.co/quasar/) 
    (thanks to the help of @pron). 
  * [reactor](reactive/kotlinx-coroutines-reactor): Replaced deprecated `setCancellation` with `onDipose` and 
    updated to Aluminium-SR3 release (courtesy of @yxf07, see #96) 
  * [jdk8](integration/kotlinx-coroutines-jdk8): Added adapters for `java.time` classes (courtesy of @fvasco, see #93)     

## Version 0.17

* `CompletableDeferred` is introduced as a set-once event-like communication primitive (see #70).
  * [Coroutines guide](docs/topics/coroutines-guide.md) uses it in a section on actors.
  * `CompletableDeferred` is an interface with private impl (courtesy of @fvasco, see #86).
  * It extends `Deferred` interface with `complete` and `completeExceptionally` functions.
* `Job.join` and `Deferred.await` wait until a cancelled coroutine stops execution (see #64). 
  * `Job` and `Deferred` have a new _cancelling_ state which they enter on invocation of `cancel`.
  * `Job.invokeOnCompletion` has an additional overload with `onCancelling: Boolean` parameter to 
    install handlers that are fired as soon as coroutine enters _cancelling_ state as opposed
    to waiting until it _completes_.
  * Internal `select` implementation is refactored to decouple it from `JobSupport` internal class 
    and to optimize its state-machine.  
  * Internal `AbstractCoroutine` class is refactored so that it is extended only by true coroutines, 
    all of which support the new _cancelling_ state.  
* `CoroutineScope.context` is renamed to `coroutineContext` to avoid conflicts with other usages of `context`
  in applications (like Android context, see #75).       
* `BroadcastChannel.open` is renamed to `openSubscription` (see #54).
* Fixed `StackOverflowError` in a convoy of `Mutex.unlock` invokers with `Unconfined` dispatcher (see #80).
* Fixed `SecurityException` when trying to use coroutines library with installed `SecurityManager`.
* Fixed a bug in `withTimeoutOrNull` in case with nested timeouts when coroutine was cancelled before it was
  ever suspended.
* Fixed a minor problem with `awaitFirst` on reactive streams that would have resulted in spurious stack-traces printed
  on the console when used with publishers/observables that continue to invoke `onNext` despite being cancelled/disposed 
  (which they are technically allowed to do by specification). 
* All factory functions for various interfaces are implemented as top-level functions
  (affects `Job`, `Channel`, `BroadcastChannel`, `Mutex`, `EventLoop`, and `CoroutineExceptionHandler`). 
  Previous approach of using `operator invoke` on their companion objects is deprecated. 
* Nicer-to-use debug `toString` implementations for coroutine dispatcher tasks and continuations.  
* A default dispatcher for `delay` is rewritten and now shares code with `EventLoopImpl` that is used by 
  `runBlocking`. It internally supports non-default `TimeSource` so that delay-using tests can be written 
  with "virtual time" by replacing their time source for the duration of tests (this feature is not available
  outside of the library).

## Version 0.16

* Coroutines that are scheduled for execution are cancellable by default now
  * `suspendAtomicCancellableCoroutine` function is introduced for funs like
    `send`/`receive`/`receiveOrNull` that require atomic cancellation
    (they cannot be cancelled after decision was made)
  * Coroutines started with default mode using
    `async`/`launch`/`actor` builders can be cancelled before their execution starts
  * `CoroutineStart.ATOMIC` is introduced as a start mode to specify that
    coroutine cannot be cancelled before its execution starts
  * `run` function is also cancellable in the same way and accepts an optional
    `CoroutineStart` parameter to change this default.
* `BroadcastChannel` factory function is introduced
* `CoroutineExceptionHandler` factory function is introduced by @konrad-kaminski
* [`integration`](integration) directory is introduced for all 3rd party integration projects
  * It has [contribution guidelines](integration/README.md#contributing) and contributions from community are welcome
  * Support for Guava `ListenableFuture` in the new [`kotlinx-coroutines-guava`](integration/kotlinx-coroutines-guava) module
  * Rx1 Scheduler support by @konrad-kaminski
* Fixed a number of `Channel` and `BroadcastChannel` implementation bugs related to concurrent 
  send/close/close of channels that lead to hanging send, offer or close operations (see #66). 
  Thanks to @chrisly42 and @cy6erGn0m for finding them.
* Fixed `withTimeoutOrNull` which was returning `null` on timeout of inner or outer `withTimeout` blocks (see #67).
  Thanks to @gregschlom for finding the problem.
* Fixed a bug where `Job` fails to dispose a handler when it is the only handler by @uchuhimo

## Version 0.15

* Switched to Kotlin version 1.1.2 (can still be used with 1.1.0).
* `CoroutineStart` enum is introduced for `launch`/`async`/`actor` builders:
  * The usage of `luanch(context, start = false)` is deprecated and is replaced with 
    `launch(context, CoroutineStart.LAZY)`
  * `CoroutineStart.UNDISPATCHED` is introduced to start coroutine execution immediately in the invoker thread,
     so that `async(context, CoroutineStart.UNDISPATCHED)` is similar to the behavior of C# `async`.
  * [Guide to UI programming with coroutines](ui/coroutines-guide-ui.md) mentions the use of it to optimize
    the start of coroutines from UI threads.
* Introduced `BroadcastChannel` interface in `kotlinx-coroutines-core` module:
  * It extends `SendChannel` interface and provides `open` function to create subscriptions.
  * Subscriptions are represented with `SubscriptionReceiveChannel` interface. 
  * The corresponding `SubscriptionReceiveChannel` interfaces are removed from [reactive](reactive) implementation
     modules. They use an interface defined in `kotlinx-coroutines-core` module.
  * `ConflatedBroadcastChannel` implementation is provided for state-observation-like use-cases, where a coroutine or a
     regular code (in UI, for example) updates the state that subscriber coroutines shall react to.
  * `ArrayBroadcastChannel` implementation is provided for event-bus-like use-cases, where a sequence of events shall
     be received by multiple subscribers without any omissions.
  * [Guide to reactive streams with coroutines](reactive/coroutines-guide-reactive.md) includes 
    "Rx Subject vs BroadcastChannel" section.
* Pull requests from Konrad Kamiński are merged into reactive stream implementations:
  * Support for Project Reactor `Mono` and `Flux`. 
    See [`kotlinx-coroutines-reactor`](reactive/kotlinx-coroutines-reactor) module.
  * Implemented Rx1 `Completable.awaitCompleted`.
  * Added support for Rx2 `Maybe`.
* Better timeout support:  
  * Introduced `withTimeoutOrNull` function.
  * Implemented `onTimeout` clause for `select` expressions.
  * Fixed spurious concurrency inside `withTimeout` blocks on their cancellation. 
  * Changed behavior of `withTimeout` when `CancellationException` is suppressed inside the block. 
    Invocation of `withTimeout` now always returns the result of execution of its inner block.
* The `channel` property in `ActorScope` is promoted to a wider `Channel` type, so that an actor
  can have an easy access to its own inbox send channel.
* Renamed `Mutex.withMutex` to `Mutex.withLock`, old name is deprecated.  

## Version 0.14
 
* Switched to Kotlin version 1.1.1 (can still be used with 1.1.0).
* Introduced `consumeEach` helper function for channels and reactive streams, Rx 1.x, and Rx 2.x.
  * It ensures that streams are unsubscribed from on any exception.
  * Iteration with `for` loop on reactive streams is **deprecated**.
  * [Guide to reactive streams with coroutines](reactive/coroutines-guide-reactive.md) is updated virtually
    all over the place to reflect these important changes.
* Implemented `awaitFirstOrDefault` extension for reactive streams, Rx 1.x, and Rx 2.x.
* Added `Mutex.withMutex` helper function.
* `kotlinx-coroutines-android` module has `provided` dependency on of Android APIs to 
  eliminate warnings when using it in android project.

## Version 0.13

* New `kotlinx-coroutinex-android` module with Android `UI` context implementation. 
* Introduced `whileSelect` convenience function.
* Implemented `ConflatedChannel`.  
* Renamed various `toXXX` conversion functions to `asXXX` (old names are deprecated).
* `run` is optimized with fast-path case and no longer has `CoroutineScope` in its block.
* Fixed dispatching logic of `withTimeout` (removed extra dispatch).
* `EventLoop` that is used by `runBlocking` now implements Delay, giving more predictable test behavior.
* Various refactorings related to resource management and timeouts:
  * `Job.Registration` is renamed to `DisposableHandle`.
  * `EmptyRegistration` is renamed to `NonDisposableHandle`.
  * `Job.unregisterOnCompletion` is renamed to `Job.disposeOnCompletion`.
  * `Delay.invokeOnTimeout` is introduced.
  * `withTimeout` now uses `Delay.invokeOnTimeout` when available.
* A number of improvement for reactive streams and Rx:
  * Introduced `rxFlowable` builder for Rx 2.x.
  * `Scheduler.asCoroutineDispatcher` extension for Rx 2.x.
  * Fixed bug with sometimes missing `onComplete` in `publish`, `rxObservable`, and `rxFlowable` builders.
  * Channels that are open for reactive streams are now `Closeable`.
  * Fixed `CompletableSource.await` and added test for it.
  * Removed `rx.Completable.await` due to name conflict.
* New documentation:
  * [Guide to UI programming with coroutines](ui/coroutines-guide-ui.md)
  * [Guide to reactive streams with coroutines](reactive/coroutines-guide-reactive.md)
* Code is published to JCenter repository.

## Version 0.12

* Switched to Kotlin version 1.1.0 release.
* Reworked and updated utilities for 
  [Reactive Streams](kotlinx-coroutines-reactive), 
  [Rx 1.x](kotlinx-coroutines-rx1), and 
  [Rx 2.x](kotlinx-coroutines-rx2) with library-specific 
  coroutine builders, suspending functions, converters and iteration support.
* `LinkedListChannel` with unlimited buffer (`offer` always succeeds).
* `onLock` select clause and an optional `owner` parameter in all `Mutex` functions.
* `selectUnbiased` function.
* `actor` coroutine builder.
* Couple more examples for "Shared mutable state and concurrency" section and 
  "Channels are fair" section with ping-pong table example 
  in [coroutines guide](docs/topics/coroutines-guide.md).

## Version 0.11-rc

* `select` expression with onJoin/onAwait/onSend/onReceive clauses.
* `Mutex` is moved to `kotlinx.coroutines.sync` package.
* `ClosedSendChannelException` is a subclass of `CancellationException` now.
* New sections on "Shared mutable state and concurrency" and "Select expression" 
  in [coroutines guide](docs/topics/coroutines-guide.md).

## Version 0.10-rc

* Switched to Kotlin version 1.1.0-rc-91.
* `Mutex` synchronization primitive is introduced.
* `buildChannel` is renamed to `produce`, old name is deprecated.
* `Job.onCompletion` is renamed to `Job.invokeOnCompletion`, old name is deprecated.
* `delay` implementation in Swing, JavaFx, and scheduled executors is fixed to avoid an extra dispatch.
* `CancellableContinuation.resumeUndispatched` is introduced to make this efficient implementation possible.
* Remove unnecessary creation of `CancellationException` to improve performance, plus other performance improvements.
* Suppress deprecated and internal APIs from docs.
* Better docs at top level with categorized summary of classes and functions.

## Version 0.8-beta

* `defer` coroutine builder is renamed to `async`.
* `lazyDefer` is deprecated, `async` has an optional `start` parameter instead.
* `LazyDeferred` interface is deprecated, lazy start functionality is integrated into `Job` interface.
* `launch` has an optional `start` parameter for lazily started coroutines.
* `Job.start` and `Job.isCompleted` are introduced.
* `Deferred.isCompletedExceptionally` and `Deferred.isCancelled` are introduced.
* `Job.getInactiveCancellationException` is renamed to `getCompletionException`.
* `Job.join` is now a member function.
* Internal `JobSupport` state machine is enhanced to support _new_ (not-started-yet) state.
  So, lazy coroutines do not need a separate state variable to track their started/not-started (new/active) status.
* Exception transparency in `Job.cancel` (original cause is rethrown).
* Clarified possible states for `Job`/`CancellableContinuation`/`Deferred` in docs.
* Example on async-style functions and links to API reference site from [coroutines guide](docs/topics/coroutines-guide.md).

## Version 0.7-beta

* Buffered and unbuffered channels are introduced: `Channel`, `SendChannel`, and `ReceiveChannel` interfaces,
  `RendezvousChannel` and `ArrayChannel` implementations, `Channel()` factory function and `buildChannel{}`
  coroutines builder.
* `Here` context is renamed to `Unconfined` (the old name is deprecated).
* A [guide on coroutines](docs/topics/coroutines-guide.md) is expanded: sections on contexts and channels.  
 
## Version 0.6-beta

* Switched to Kotlin version 1.1.0-beta-37.
* A [guide on coroutines](docs/topics/coroutines-guide.md) is expanded.  

## Version 0.5-beta

* Switched to Kotlin version 1.1.0-beta-22 (republished version).
* Removed `currentCoroutineContext` and related thread-locals without replacement.
  Explicitly pass coroutine context around if needed.
* `lazyDefer(context) {...}` coroutine builder and `LazyDeferred` interface are introduced.
* The default behaviour of all coroutine dispatchers is changed to always schedule execution of new coroutine 
  for later in this thread or thread pool. Correspondingly, `CoroutineDispatcher.isDispatchNeeded` function
  has a default implementation that returns `true`.
* `NonCancellable` context is introduced.  
* Performance optimizations for cancellable continuations (fewer objects created).
* A [guide on coroutines](docs/topics/coroutines-guide.md) is added.  

## Version 0.4-beta

* Switched to Kotlin version 1.1.0-beta-18 (republished version).
* `CoroutineDispatcher` methods now have `context` parameter.
* Introduced `CancellableContinuation.isCancelled`
* Introduced `EventLoop` dispatcher and made it a default for `runBlocking { ... }`
* Introduced `CoroutineScope` interface with `isActive` and `context` properties; 
  standard coroutine builders include it as receiver for convenience.
* Introduced `Executor.toCoroutineDispatcher()` extension.  
* Delay scheduler thread is not daemon anymore, but times out automatically.
* Debugging facilities in `newCoroutineContext` can be explicitly disabled with `-Dkotlinx.coroutines.debug=off`.
* xxx-test files are renamed to xxx-example for clarity.
* Fixed NPE in Job implementation when starting coroutine with already cancelled parent job.
* Support cancellation in `kotlinx-coroutines-nio` module
