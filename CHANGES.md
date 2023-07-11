# Change log for kotlinx.coroutines

## Version 1.7.2

### Bug fixes and improvements

* Coroutines debugger no longer keeps track of coroutines with empty coroutine context (#3782).
* `CopyableThreadContextElement` now properly copies an element when crossing the coroutine boundary in `flowOn` (#3787). Thanks @wanyingd1996!
* Coroutine timeouts no longer prevent K/N `newSingleThreadContext` from closing (#3768).
* A non-linearizability in `Mutex` during `tryLock`/`unlock` sequence with owners is fixed (#3745).
* Atomicfu version is updated to 0.21.0.

## Version 1.7.1

### Bug fixes and improvements

* Special characters in coroutine names in JSON dumps are supported (#3747)
* The binary compatibility of the experimental overload of `runTest` is restored (#3673)
* Channels that don't use `onUndeliveredElement` now allocate less memory (#3646)

## Version 1.7.0

### Core API significant improvements

* New `Channel` implementation with significant performance improvements across the API (#3621).
* New `select` operator implementation: faster, more lightweight, and more robust (#3020).
* `Mutex` and `Semaphore` now share the same underlying data structure (#3020).
* `Dispatchers.IO` is added to K/N (#3205)
  * `newFixedThreadPool` and `Dispatchers.Default` implementations on K/N were wholly rewritten to support graceful growth under load (#3595).
* `kotlinx-coroutines-test` rework:
  - Add the `timeout` parameter to `runTest` for the whole-test timeout, 10 seconds by default (#3270). This replaces the configuration of quiescence timeouts, which is now deprecated (#3603).
  - The `withTimeout` exception messages indicate if the timeout used the virtual time (#3588).
  - `TestCoroutineScheduler`, `runTest`, and `TestScope` API are promoted to stable (#3622).
  - `runTest` now also fails if there were uncaught exceptions in coroutines not inherited from the test coroutine (#1205).

### Breaking changes

* Old K/N memory model is no longer supported (#3375).
* New generic upper bounds were added to reactive integration API where the language since 1.8.0 dictates (#3393).
* `kotlinx-coroutines-core` and `kotlinx-coroutines-jdk8` artifacts were merged into a single artifact (#3268).
* Artificial stackframes in stacktrace recovery no longer contain the `\b` symbol and are now navigable in IDE and supplied with proper documentation (#2291).
* `CoroutineContext.isActive` returns `true` for contexts without any job in them (#3300).

### Bug fixes and improvements

* Kotlin version is updated to 1.8.20
* Atomicfu version is updated to 0.20.2.
* `JavaFx` version is updated to 17.0.2 in `kotlinx-coroutines-javafx` (#3671)..
* JPMS is supported (#2237). Thanks @lion7!
* `BroadcastChannel` and all the corresponding API are deprecated (#2680).
* Added all supported K/N targets (#3601, #812, #855).
* K/N `Dispatchers.Default` is backed by the number of threads equal to the number of available cores (#3366).
* Fixed an issue where some coroutines' internal exceptions were not properly serializable (#3328).
* Introduced `Job.parent` API (#3201).
* Fixed a bug when `TestScheduler` leaked cancelled jobs (#3398).
* `TestScope.timeSource` now provides comparable time marks (#3617). Thanks @hfhbd!
* Fixed an issue when cancelled `withTimeout` handles were preserved in JS runtime (#3440).
* Ensure `awaitFrame` only awaits a single frame when used from the main looper (#3432). Thanks @pablobaxter!
* Obsolete `Class-Path` attribute was removed from `kotlinx-coroutines-debug.jar` manifest (#3361).
* Fixed a bug when `updateThreadContext` operated on the parent context (#3411).
* Added new `Flow.filterIsInstance` extension (#3240).
* `Dispatchers.Default` thread name prefixes are now configurable with system property (#3231).
* Added `Flow.timeout` operator as `@FlowPreview` (#2624). Thanks @pablobaxter!
* Improved the performance of the `future` builder in case of exceptions (#3475). Thanks @He-Pin!
* `Mono.awaitSingleOrNull` now waits for the `onComplete` signal (#3487).
* `Channel.isClosedForSend` and `Channel.isClosedForReceive` are promoted from experimental to delicate (#3448).
* Fixed a data race in native `EventLoop` (#3547).
* `Dispatchers.IO.limitedParallelism(valueLargerThanIOSize)` no longer creates an additional wrapper (#3442). Thanks @dovchinnikov!
* Various `@FlowPreview` and `@ExperimentalCoroutinesApi` are promoted to experimental and stable respectively (#3542, #3097, #3548).
* Performance improvements in `Dispatchers.Default` and `Dispatchers.IO` (#3416, #3418).
* Fixed a bug when internal `suspendCancellableCoroutineReusable` might have hanged (#3613).
* Introduced internal API to process events in the current system dispatcher (#3439).
* Global `CoroutineExceptionHandler` is no longer invoked in case of unprocessed `future` failure (#3452).
* Performance improvements and reduced thread-local pressure for the `withContext` operator (#3592).
* Improved performance of `DebugProbes` (#3527).
* Fixed a bug when the coroutine debugger might have detected the state of a coroutine incorrectly (#3193).
* `CoroutineDispatcher.asExecutor()` runs tasks without dispatching if the dispatcher is unconfined (#3683). Thanks @odedniv!
* `SharedFlow.toMutableList` and `SharedFlow.toSet` lints are introduced (#3706).
* `Channel.invokeOnClose` is promoted to stable API (#3358).
* Improved lock contention in `Dispatchers.Default` and `Dispatchers.IO` during the startup phase (#3652).
* Fixed a bug that led to threads oversubscription in `Dispatchers.Default` (#3642).
* Fixed a bug that allowed `limitedParallelism` to perform dispatches even after the underlying dispatcher was closed (#3672).
* Fixed a bug that prevented stacktrace recovery when the exception's constructor from `cause` was selected (#3714).
* Improved sanitizing of stracktrace-recovered traces (#3714).
* Introduced an internal flag to disable uncaught exceptions reporting in tests as a temporary migration mechanism (#3736).
* Various documentation improvements and fixes.

Changelog for previous versions may be found in [CHANGES_UP_TO_1.7.md](CHANGES_UP_TO_1.7.md)
