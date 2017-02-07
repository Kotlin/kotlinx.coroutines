# Module kotlinx-coroutines-core

Core primitives to work with coroutines.
 
# Package kotlinx.coroutines.experimental

General-purpose coroutine builders and contexts.

* `launch(context) {...}` to start a coroutine in the given context and get reference to its `Job`.
* `run(context) {...}` to switch to a different context inside a coroutine.
* `runBlocking {...}` to use asynchronous Kotlin APIs from a thread-blocking code.  
* `defer(context) {...}` and `lazyDefer(context) {...}` to get a deferred result of coroutine execution in a 
   non-blocking way via a light-weight future interface called `Deferred`.
* `delay(...)` for a non-blocking sleep in coroutines and 
  `yield()` to release a thread in single-threaded dispatchers.
* `withTimeout(timeout) {...}` scope function to easily set coroutine time-limit (deadline),
   and `NonCancellable` context to avoid it when needed.
* `CommonPool` and `Unconfined` contexts, access to `context` of a parent coroutine in its `CoroutineScope`.
* `newSingleThreadContext(...)` and `newFixedThreadPoolContext(...)` functions, 
  `Executor.toCoroutineDispatcher()` extension.
* Cancellation support with `Job` interface and `suspendCancellableCoroutine` helper function.
* Debugging facilities for coroutines (run JVM with `-ea` or `-Dkotlinx.coroutines.debug` options) and
  `newCoroutineContext(context)` function to write user-defined coroutine builders that work with these
   debugging facilities.

# Package kotlinx.coroutines.experimental.channels

Channels -- non-blocking primitives for communicating a stream of values between coroutines.

* `Channel`, `SendChannel`, and `ReceiveChannel` interfaces,
* `RendezvousChannel` (unbuffered) and `ArrayChannel` (buffered) implementations
* `Channel()` factory function and `buildChannel{}` coroutines builder.
