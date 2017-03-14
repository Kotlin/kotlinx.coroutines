# Change log for kotlinx.coroutines 

## Version 0.13

* New `kotlinx-coroutinex-android` module with Android `UI` context implementation 
* Introduced `whileSelect` convenience function
* Implemented `ConflatedChannel`  
* Renamed various `toXXX` conversion functions to `asXXX` (old names are deprecated)
* `run` is optimized with fast-path case and no longer has `CoroutineScope` in its block
* Fixed dispatching logic of `withTimeout` (removed extra dispatch)
* `EventLoop` that is used by `runBlocking` now implements Delay, giving more predictable test behavior
* Various refactorings related to resource management and timeouts:
  * `Job.Registration` is renamed to `DisposableHandle`
  * `EmptyRegistration` is renamed to `NonDisposableHandle`
  * `Job.unregisterOnCompletion` is renamed to `Job.disposeOnCompletion`
  * `Delay.invokeOnTimeout` is introduced
  * `withTimeout` now uses `Delay.invokeOnTimeout` when available
* A number of improvement for reactive streams and Rx:
  * Introduced `rxFlowable` builder for Rx 2.x
  * `Scheduler.asCoroutineDispatcher` extension for Rx 2.x
  * Fixed bug with sometimes missing `onComplete` in `publish`, `rxObservable`, and `rxFlowable` builders
  * Channels that are open for reactive streams are now `Closeable`
  * Fixed `CompletableSource.await` and added test for it
  * Removed `rx.Completable.await` due to name conflict
* New documentation:
  * [Guide to UI programming with coroutines](ui/coroutines-guide-ui.md)
  * [Guide to reactive streams with coroutines](reactive/coroutines-guide-reactive.md)
* Code is published to JCenter repository  

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
  in [coroutines guide](coroutines-guide.md).

## Version 0.11-rc

* `select` expression with onJoin/onAwait/onSend/onReceive clauses.
* `Mutex` is moved to `kotlinx.coroutines.experimental.sync` package.
* `ClosedSendChannelException` is a subclass of `CancellationException` now.
* New sections on "Shared mutable state and concurrency" and "Select expression" 
  in [coroutines guide](coroutines-guide.md).

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
* Example on async-style functions and links to API reference site from [coroutines guide](coroutines-guide.md).

## Version 0.7-beta

* Buffered and unbuffered channels are introduced: `Channel`, `SendChannel`, and `ReceiveChannel` interfaces,
  `RendezvousChannel` and `ArrayChannel` implementations, `Channel()` factory function and `buildChannel{}`
  coroutines builder.
* `Here` context is renamed to `Unconfined` (the old name is deprecated).
* A [guide on coroutines](coroutines-guide.md) is expanded: sections on contexts and channels.  
 
## Version 0.6-beta

* Switched to Kotlin version 1.1.0-beta-37.
* A [guide on coroutines](coroutines-guide.md) is expanded.  

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
* A [guide on coroutines](coroutines-guide.md) is added.  

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
