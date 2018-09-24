# Module kotlinx-coroutines-core

Core primitives to work with coroutines.

Coroutine builder functions:

| **Name**      | **Result**    | **Scope**        | **Description**
| ------------- | ------------- | ---------------- | ---------------
| [launch]      | [Job]         | [CoroutineScope] | Launches coroutine that does not have any result 
| [async]       | [Deferred]    | [CoroutineScope] | Returns a single value with the future result
| [produce][kotlinx.coroutines.experimental.channels.produce]     | [ReceiveChannel][kotlinx.coroutines.experimental.channels.ReceiveChannel] | [ProducerScope][kotlinx.coroutines.experimental.channels.ProducerScope]  | Produces a stream of elements
| [actor][kotlinx.coroutines.experimental.channels.actor]     | [SendChannel][kotlinx.coroutines.experimental.channels.SendChannel] | [ActorScope][kotlinx.coroutines.experimental.channels.ActorScope]  | Processes a stream of messages
| [runBlocking] | `T`           | [CoroutineScope] | Blocks the thread while the coroutine runs

Coroutine dispatchers implementing [CoroutineDispatcher]:
 
| **Name**                    | **Description**
| --------------------------- | ---------------
| [Dispatchers.Default]       | Confines coroutine execution to a shared pool of background threads
| [Dispatchers.Unconfined]    | Does not confine coroutine execution in any way
| [newSingleThreadContext]    | Create new single-threaded coroutine context
| [newFixedThreadPoolContext] | Creates new thread pool of a fixed size 
| [Executor.asCoroutineDispatcher][java.util.concurrent.Executor.asCoroutineDispatcher] | Extension to convert any executor

More context elements:

| **Name**                    | **Description**
| --------------------------- | ---------------
| [NonCancellable]            | A non-cancelable job that is always active
| [CoroutineExceptionHandler] | Handler for uncaught exception

Synchronization primitives for coroutines:

| **Name**   | **Suspending functions**                                    | **Description**
| ---------- | ----------------------------------------------------------- | ---------------
| [Mutex][kotlinx.coroutines.experimental.sync.Mutex]          | [lock][kotlinx.coroutines.experimental.sync.Mutex.lock]                                          | Mutual exclusion 
| [Channel][kotlinx.coroutines.experimental.channels.Channel]  | [send][kotlinx.coroutines.experimental.channels.SendChannel.send], [receive][kotlinx.coroutines.experimental.channels.ReceiveChannel.receive] | Communication channel (aka queue or exchanger)

Top-level suspending functions:

| **Name**                 | **Description**
| -------------------      | ---------------
| [delay]                  | Non-blocking sleep
| [yield]                  | Yields thread in single-threaded dispatchers
| [withContext]            | Switches to a different context
| [withTimeout]            | Set execution time-limit with exception on timeout 
| [withTimeoutOrNull]      | Set execution time-limit will null result on timeout
| [awaitAll]               | Awaits for successful completion of all given jobs or exceptional completion of any
| [joinAll]                | Joins on all given jobs

Cancellation support for user-defined suspending functions is available with [suspendCancellableCoroutine]
helper function. [NonCancellable] job object is provided to suppress cancellation with 
`withContext(NonCancellable) {...}` block of code.

[Select][kotlinx.coroutines.experimental.selects.select] expression waits for the result of multiple suspending functions simultaneously:

| **Receiver**     | **Suspending function**                       | **Select clause**                                | **Non-suspending version**
| ---------------- | --------------------------------------------- | ------------------------------------------------ | --------------------------
| [Job]            | [join][Job.join]                              | [onJoin][Job.onJoin]                   | [isCompleted][Job.isCompleted]
| [Deferred]       | [await][Deferred.await]                       | [onAwait][Deferred.onAwait]                 | [isCompleted][Job.isCompleted]
| [SendChannel][kotlinx.coroutines.experimental.channels.SendChannel]    | [send][kotlinx.coroutines.experimental.channels.SendChannel.send]                      | [onSend][kotlinx.coroutines.experimental.channels.SendChannel.onSend]                   | [offer][kotlinx.coroutines.experimental.channels.SendChannel.offer]
| [ReceiveChannel][kotlinx.coroutines.experimental.channels.ReceiveChannel] | [receive][kotlinx.coroutines.experimental.channels.ReceiveChannel.receive]             | [onReceive][kotlinx.coroutines.experimental.channels.ReceiveChannel.onReceive]             | [poll][kotlinx.coroutines.experimental.channels.ReceiveChannel.poll]
| [ReceiveChannel][kotlinx.coroutines.experimental.channels.ReceiveChannel] | [receiveOrNull][kotlinx.coroutines.experimental.channels.ReceiveChannel.receiveOrNull] | [onReceiveOrNull][kotlinx.coroutines.experimental.channels.ReceiveChannel.onReceiveOrNull] | [poll][kotlinx.coroutines.experimental.channels.ReceiveChannel.poll]
| [Mutex][kotlinx.coroutines.experimental.sync.Mutex]          | [lock][kotlinx.coroutines.experimental.sync.Mutex.lock]                            | [onLock][kotlinx.coroutines.experimental.sync.Mutex.onLock]                   | [tryLock][kotlinx.coroutines.experimental.sync.Mutex.tryLock]
| none            | [delay]                                        | [onTimeout][kotlinx.coroutines.experimental.selects.SelectBuilder.onTimeout]                   | none

This module provides debugging facilities for coroutines (run JVM with `-ea` or `-Dkotlinx.coroutines.debug` options) 
and [newCoroutineContext] function to write user-defined coroutine builders that work with these
debugging facilities.

This module provides a special CoroutineContext type [TestCoroutineCoroutineContext][kotlinx.coroutines.experimental.test.TestCoroutineContext] that
allows the writer of code that contains Coroutines with delays and timeouts to write non-flaky unit-tests for that code allowing these tests to
terminate in near zero time. See the documentation for this class for more information.

# Package kotlinx.coroutines.experimental

General-purpose coroutine builders, contexts, and helper functions.

# Package kotlinx.coroutines.experimental.sync

Synchronization primitives (mutex).

# Package kotlinx.coroutines.experimental.channels

Channels -- non-blocking primitives for communicating a stream of elements between coroutines.

# Package kotlinx.coroutines.experimental.selects

Select expression to perform multiple suspending operations simultaneously until one of them succeeds.

# Package kotlinx.coroutines.experimental.intrinsics

Low-level primitives for finer-grained control of coroutines.

# Package kotlinx.coroutines.experimental.timeunit

Optional time unit support for multiplatform projects.

# Package kotlinx.coroutines.experimental.test

Components to ease writing unit-tests for code that contains coroutines with delays and timeouts.

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines.experimental -->
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/launch.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/index.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-scope/index.html
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/async.html
[Deferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-deferred/index.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/run-blocking.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-dispatcher/index.html
[Dispatchers.Default]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-dispatchers/-default.html
[Dispatchers.Unconfined]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-dispatchers/-unconfined.html
[newSingleThreadContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/new-single-thread-context.html
[newFixedThreadPoolContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/new-fixed-thread-pool-context.html
[java.util.concurrent.Executor.asCoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/java.util.concurrent.-executor/as-coroutine-dispatcher.html
[NonCancellable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-non-cancellable.html
[CoroutineExceptionHandler]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-coroutine-exception-handler/index.html
[delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/delay.html
[yield]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/yield.html
[withContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/with-context.html
[withTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/with-timeout.html
[withTimeoutOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/with-timeout-or-null.html
[awaitAll]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/await-all.html
[joinAll]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/join-all.html
[suspendCancellableCoroutine]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/suspend-cancellable-coroutine.html
[Job.join]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/join.html
[Job.onJoin]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/on-join.html
[Job.isCompleted]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-job/is-completed.html
[Deferred.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-deferred/await.html
[Deferred.onAwait]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/-deferred/on-await.html
[newCoroutineContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental/new-coroutine-context.html
<!--- INDEX kotlinx.coroutines.experimental.sync -->
[kotlinx.coroutines.experimental.sync.Mutex]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.sync/-mutex/index.html
[kotlinx.coroutines.experimental.sync.Mutex.lock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.sync/-mutex/lock.html
[kotlinx.coroutines.experimental.sync.Mutex.onLock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.sync/-mutex/on-lock.html
[kotlinx.coroutines.experimental.sync.Mutex.tryLock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.sync/-mutex/try-lock.html
<!--- INDEX kotlinx.coroutines.experimental.channels -->
[kotlinx.coroutines.experimental.channels.produce]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/produce.html
[kotlinx.coroutines.experimental.channels.ReceiveChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/index.html
[kotlinx.coroutines.experimental.channels.ProducerScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-producer-scope/index.html
[kotlinx.coroutines.experimental.channels.actor]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/actor.html
[kotlinx.coroutines.experimental.channels.SendChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-send-channel/index.html
[kotlinx.coroutines.experimental.channels.ActorScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-actor-scope/index.html
[kotlinx.coroutines.experimental.channels.Channel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-channel/index.html
[kotlinx.coroutines.experimental.channels.SendChannel.send]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-send-channel/send.html
[kotlinx.coroutines.experimental.channels.ReceiveChannel.receive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/receive.html
[kotlinx.coroutines.experimental.channels.SendChannel.onSend]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-send-channel/on-send.html
[kotlinx.coroutines.experimental.channels.SendChannel.offer]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-send-channel/offer.html
[kotlinx.coroutines.experimental.channels.ReceiveChannel.onReceive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/on-receive.html
[kotlinx.coroutines.experimental.channels.ReceiveChannel.poll]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/poll.html
[kotlinx.coroutines.experimental.channels.ReceiveChannel.receiveOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/receive-or-null.html
[kotlinx.coroutines.experimental.channels.ReceiveChannel.onReceiveOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.channels/-receive-channel/on-receive-or-null.html
<!--- INDEX kotlinx.coroutines.experimental.selects -->
[kotlinx.coroutines.experimental.selects.select]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.selects/select.html
[kotlinx.coroutines.experimental.selects.SelectBuilder.onTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.selects/-select-builder/on-timeout.html
<!--- INDEX kotlinx.coroutines.experimental.test -->
[kotlinx.coroutines.experimental.test.TestCoroutineContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.experimental.test/-test-coroutine-context/index.html
<!--- END -->
