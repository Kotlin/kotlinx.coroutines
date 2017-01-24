# kotlinx.coroutines change log

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
