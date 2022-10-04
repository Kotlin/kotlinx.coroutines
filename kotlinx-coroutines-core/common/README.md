# Module kotlinx-coroutines-core

Core primitives to work with coroutines available on all platforms.

Coroutine builder functions:

| **Name**      | **Result**    | **Scope**        | **Description**
| ------------- | ------------- | ---------------- | ---------------
| [launch]      | [Job]         | [CoroutineScope] | Launches coroutine that does not have any result 
| [async]       | [Deferred]    | [CoroutineScope] | Returns a single value with the future result
| [produce][kotlinx.coroutines.channels.produce]     | [ReceiveChannel][kotlinx.coroutines.channels.ReceiveChannel] | [ProducerScope][kotlinx.coroutines.channels.ProducerScope]  | Produces a stream of elements
| [actor][kotlinx.coroutines.channels.actor]     | [SendChannel][kotlinx.coroutines.channels.SendChannel] | [ActorScope][kotlinx.coroutines.channels.ActorScope]  | Processes a stream of messages

Coroutine dispatchers implementing [CoroutineDispatcher]:
 
| **Name**                    | **Description**
| --------------------------- | ---------------
| [Dispatchers.Default]       | Confines coroutine execution to a shared pool of background threads
| [Dispatchers.Unconfined]    | Does not confine coroutine execution in any way
| [newSingleThreadContext]    | Creates a single-threaded coroutine context
| [newFixedThreadPoolContext] | Creates a thread pool of a fixed size 
| [Executor.asCoroutineDispatcher][asCoroutineDispatcher] | Extension to convert any executor

More context elements:

| **Name**                    | **Description**
| --------------------------- | ---------------
| [NonCancellable]            | A non-cancelable job that is always active
| [CoroutineExceptionHandler] | Handler for uncaught exception

Synchronization primitives for coroutines:

| **Name**   | **Suspending functions**                                    | **Description**
| ---------- | ----------------------------------------------------------- | ---------------
| [Mutex][kotlinx.coroutines.sync.Mutex]          | [lock][kotlinx.coroutines.sync.Mutex.lock]                                          | Mutual exclusion 
| [Channel][kotlinx.coroutines.channels.Channel]  | [send][kotlinx.coroutines.channels.SendChannel.send], [receive][kotlinx.coroutines.channels.ReceiveChannel.receive] | Communication channel (aka queue or exchanger)

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

[Select][kotlinx.coroutines.selects.select] expression waits for the result of multiple suspending functions simultaneously:

| **Receiver**     | **Suspending function**                       | **Select clause**                                | **Non-suspending version**
| ---------------- | --------------------------------------------- | ------------------------------------------------ | --------------------------
| [Job]            | [join][Job.join]                              | [onJoin][Job.onJoin]                   | [isCompleted][Job.isCompleted]
| [Deferred]       | [await][Deferred.await]                       | [onAwait][Deferred.onAwait]                 | [isCompleted][Job.isCompleted]
| [SendChannel][kotlinx.coroutines.channels.SendChannel]    | [send][kotlinx.coroutines.channels.SendChannel.send]                      | [onSend][kotlinx.coroutines.channels.SendChannel.onSend]                   | [trySend][kotlinx.coroutines.channels.SendChannel.trySend]
| [ReceiveChannel][kotlinx.coroutines.channels.ReceiveChannel] | [receive][kotlinx.coroutines.channels.ReceiveChannel.receive]             | [onReceive][kotlinx.coroutines.channels.ReceiveChannel.onReceive]             | [tryReceive][kotlinx.coroutines.channels.ReceiveChannel.tryReceive]
| [ReceiveChannel][kotlinx.coroutines.channels.ReceiveChannel] | [receiveCatching][kotlinx.coroutines.channels.ReceiveChannel.receiveCatching] | [onReceiveCatching][kotlinx.coroutines.channels.ReceiveChannel.onReceiveCatching] | [tryReceive][kotlinx.coroutines.channels.ReceiveChannel.tryReceive]
| none            | [delay]                                        | [onTimeout][kotlinx.coroutines.selects.SelectBuilder.onTimeout]                   | none

This module provides debugging facilities for coroutines (run JVM with `-ea` or `-Dkotlinx.coroutines.debug` options) 
and [newCoroutineContext] function to write user-defined coroutine builders that work with these
debugging facilities. See [DEBUG_PROPERTY_NAME] for more details.

# Package kotlinx.coroutines

General-purpose coroutine builders, contexts, and helper functions.

# Package kotlinx.coroutines.flow

Flow -- primitive to work with asynchronous and event-based streams of data.

# Package kotlinx.coroutines.sync

Synchronization primitives (mutex).

# Package kotlinx.coroutines.channels

Channels -- non-blocking primitives for communicating a stream of elements between coroutines.

# Package kotlinx.coroutines.selects

Select expression to perform multiple suspending operations simultaneously until one of them succeeds.

# Package kotlinx.coroutines.intrinsics

Low-level primitives for finer-grained control of coroutines.

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->

[launch]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html
[Job]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[CoroutineScope]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[async]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html
[Deferred]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/index.html
[CoroutineDispatcher]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
[Dispatchers.Default]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html
[Dispatchers.Unconfined]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-unconfined.html
[newSingleThreadContext]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/new-single-thread-context.html
[newFixedThreadPoolContext]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/new-fixed-thread-pool-context.html
[asCoroutineDispatcher]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/as-coroutine-dispatcher.html
[NonCancellable]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-non-cancellable/index.html
[CoroutineExceptionHandler]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-exception-handler/index.html
[delay]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html
[yield]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/yield.html
[withContext]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html
[withTimeout]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout.html
[withTimeoutOrNull]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout-or-null.html
[awaitAll]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/await-all.html
[joinAll]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/join-all.html
[suspendCancellableCoroutine]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/suspend-cancellable-coroutine.html
[Job.join]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/join.html
[Job.onJoin]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/on-join.html
[Job.isCompleted]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/is-completed.html
[Deferred.await]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/await.html
[Deferred.onAwait]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/on-await.html
[newCoroutineContext]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/new-coroutine-context.html
[DEBUG_PROPERTY_NAME]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-d-e-b-u-g_-p-r-o-p-e-r-t-y_-n-a-m-e.html

<!--- INDEX kotlinx.coroutines.sync -->

[kotlinx.coroutines.sync.Mutex]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/index.html
[kotlinx.coroutines.sync.Mutex.lock]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/lock.html

<!--- INDEX kotlinx.coroutines.channels -->

[kotlinx.coroutines.channels.produce]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/produce.html
[kotlinx.coroutines.channels.ReceiveChannel]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/index.html
[kotlinx.coroutines.channels.ProducerScope]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-producer-scope/index.html
[kotlinx.coroutines.channels.actor]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/actor.html
[kotlinx.coroutines.channels.SendChannel]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/index.html
[kotlinx.coroutines.channels.ActorScope]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-actor-scope/index.html
[kotlinx.coroutines.channels.Channel]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-channel/index.html
[kotlinx.coroutines.channels.SendChannel.send]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/send.html
[kotlinx.coroutines.channels.ReceiveChannel.receive]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/receive.html
[kotlinx.coroutines.channels.SendChannel.onSend]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/on-send.html
[kotlinx.coroutines.channels.SendChannel.trySend]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/try-send.html
[kotlinx.coroutines.channels.ReceiveChannel.onReceive]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/on-receive.html
[kotlinx.coroutines.channels.ReceiveChannel.tryReceive]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/try-receive.html
[kotlinx.coroutines.channels.ReceiveChannel.receiveCatching]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/receive-catching.html
[kotlinx.coroutines.channels.ReceiveChannel.onReceiveCatching]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/on-receive-catching.html

<!--- INDEX kotlinx.coroutines.selects -->

[kotlinx.coroutines.selects.select]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.selects/select.html
[kotlinx.coroutines.selects.SelectBuilder.onTimeout]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.selects/on-timeout.html

<!--- END -->
