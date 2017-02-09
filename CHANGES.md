# Change log for kotlinx.coroutines 

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
