# Module kotlinx-coroutines-core

Core primitives to work with coroutines.

Coroutine builder functions:

| **Name**                                       | **Result**                                                   | **Scope**                                                  | **Description**
| ---------------------------------------------- | ------------------------------------------------------------ | ---------------------------------------------------------- | ---------------
| [launch][kotlinx.coroutines.launch]            | [Job][kotlinx.coroutines.Job]                                | [CoroutineScope][kotlinx.coroutines.CoroutineScope]        | Launches coroutine that does not have any result 
| [async][kotlinx.coroutines.async]              | [Deferred][kotlinx.coroutines.Deferred]                      | [CoroutineScope][kotlinx.coroutines.CoroutineScope]        | Returns a single value with the future result
| [produce][kotlinx.coroutines.channels.produce] | [ReceiveChannel][kotlinx.coroutines.channels.ReceiveChannel] | [ProducerScope][kotlinx.coroutines.channels.ProducerScope] | Produces a stream of elements
| [runBlocking][kotlinx.coroutines.runBlocking]  | `T`                                                          | [CoroutineScope][kotlinx.coroutines.CoroutineScope]        | Blocks the thread while the coroutine runs

Coroutine dispatchers implementing [CoroutineDispatcher]:
 
| **Name**                                                            | **Description**
| ------------------------------------------------------------------- | ---------------
| [Dispatchers.Default][kotlinx.coroutines.Dispatchers.Default]       | Confines coroutine execution to a shared pool of background threads
| [Dispatchers.Unconfined][kotlinx.coroutines.Dispatchers.Unconfined] | Does not confine coroutine execution in any way

More context elements:

| **Name**                                                                  | **Description**
| ------------------------------------------------------------------------- | ---------------
| [NonCancellable][kotlinx.coroutines.NonCancellable]                       | A non-cancelable job that is always active
| [CoroutineExceptionHandler][kotlinx.coroutines.CoroutineExceptionHandler] | Handler for uncaught exception

Synchronization primitives for coroutines:

| **Name**                                        | **Suspending functions**                                                                                            | **Description**
| ----------------------------------------------- | ------------------------------------------------------------------------------------------------------------------- | ---------------
| [Mutex][kotlinx.coroutines.sync.Mutex]          | [lock][kotlinx.coroutines.sync.Mutex.lock]                                                                          | Mutual exclusion 
| [Channel][kotlinx.coroutines.channels.Channel]  | [send][kotlinx.coroutines.channels.SendChannel.send], [receive][kotlinx.coroutines.channels.ReceiveChannel.receive] | Communication channel (aka queue or exchanger)

Top-level suspending functions:

| **Name**                                                  | **Description**
| --------------------------------------------------------- | ---------------
| [delay][kotlinx.coroutines.delay]                         | Non-blocking sleep
| [yield][kotlinx.coroutines.yield]                         | Yields thread in single-threaded dispatchers
| [withContext][kotlinx.coroutines.withContext]             | Switches to a different context
| [withTimeout][kotlinx.coroutines.withTimeout]             | Set execution time-limit with exception on timeout 
| [withTimeoutOrNull][kotlinx.coroutines.withTimeoutOrNull] | Set execution time-limit will null result on timeout
| [awaitAll][kotlinx.coroutines.awaitAll]                   | Awaits for successful completion of all given jobs or exceptional completion of any
| [joinAll][kotlinx.coroutines.joinAll]                     | Joins on all given jobs

Cancellation support for user-defined suspending functions is available with [suspendCancellableCoroutine]
helper function. [NonCancellable] job object is provided to suppress cancellation with 
`withContext(NonCancellable) {...}` block of code.

[Select][kotlinx.coroutines.selects.select] expression waits for the result of multiple suspending functions simultaneously:

| **Receiver**                                                 | **Suspending function**                                         | **Select clause**                                                 | **Non-suspending version**
| ------------------------------------------------------------ | --------------------------------------------------------------- | ----------------------------------------------------------------- | --------------------------
| [Job][kotlinx.coroutines.Job]                                | [join][kotlinx.coroutines.Job.join]                             | [onJoin][kotlinx.coroutines.Job.onJoin]                           | [isCompleted][kotlinx.coroutines.Job.isCompleted]
| [Deferred][kotlinx.coroutines.Deferred]                      | [await][kotlinx.coroutines.Deferred.await]                      | [onAwait][kotlinx.coroutines.Deferred.onAwait]                    | [isCompleted][kotlinx.coroutines.Job.isCompleted]
| [SendChannel][kotlinx.coroutines.channels.SendChannel]       | [send][kotlinx.coroutines.channels.SendChannel.send]            | [onSend][kotlinx.coroutines.channels.SendChannel.onSend]          | [trySend][kotlinx.coroutines.channels.SendChannel.trySend]
| [ReceiveChannel][kotlinx.coroutines.channels.ReceiveChannel] | [receive][kotlinx.coroutines.channels.ReceiveChannel.receive]   | [onReceive][kotlinx.coroutines.channels.ReceiveChannel.onReceive] | [tryReceive][kotlinx.coroutines.channels.ReceiveChannel.tryReceive]
| [ReceiveChannel][kotlinx.coroutines.channels.ReceiveChannel] | [receiveCatching][kotlinx.coroutines.channels.receiveCatching]  | [onReceiveCatching][kotlinx.coroutines.channels.onReceiveCatching] | [tryReceive][kotlinx.coroutines.channels.ReceiveChannel.tryReceive]
| none                                                         | [delay][kotlinx.coroutines.delay]                               | [onTimeout][kotlinx.coroutines.selects.SelectBuilder.onTimeout]   | none

# Package kotlinx.coroutines

General-purpose coroutine builders, contexts, and helper functions.

# Package kotlinx.coroutines.sync

Synchronization primitives (mutex).

# Package kotlinx.coroutines.channels

Channels &mdash; non-blocking primitives for communicating a stream of elements between coroutines.

# Package kotlinx.coroutines.flow

Flow &mdash; asynchronous cold stream of elements.

# Package kotlinx.coroutines.selects

Select expression to perform multiple suspending operations simultaneously until one of them succeeds.

# Package kotlinx.coroutines.intrinsics

Low-level primitives for finer-grained control of coroutines.

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->

[kotlinx.coroutines.launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html
[kotlinx.coroutines.Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[kotlinx.coroutines.CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[kotlinx.coroutines.async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html
[kotlinx.coroutines.Deferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/index.html
[kotlinx.coroutines.runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
[kotlinx.coroutines.Dispatchers.Default]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html
[kotlinx.coroutines.Dispatchers.Unconfined]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-unconfined.html
[kotlinx.coroutines.NonCancellable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-non-cancellable/index.html
[kotlinx.coroutines.CoroutineExceptionHandler]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-exception-handler/index.html
[kotlinx.coroutines.delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html
[kotlinx.coroutines.yield]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/yield.html
[kotlinx.coroutines.withContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html
[kotlinx.coroutines.withTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout.html
[kotlinx.coroutines.withTimeoutOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout-or-null.html
[kotlinx.coroutines.awaitAll]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/await-all.html
[kotlinx.coroutines.joinAll]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/join-all.html
[suspendCancellableCoroutine]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/suspend-cancellable-coroutine.html
[NonCancellable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-non-cancellable/index.html
[kotlinx.coroutines.Job.join]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/join.html
[kotlinx.coroutines.Job.onJoin]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/on-join.html
[kotlinx.coroutines.Job.isCompleted]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/is-completed.html
[kotlinx.coroutines.Deferred.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/await.html
[kotlinx.coroutines.Deferred.onAwait]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/on-await.html

<!--- INDEX kotlinx.coroutines.sync -->

[kotlinx.coroutines.sync.Mutex]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/index.html
[kotlinx.coroutines.sync.Mutex.lock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/lock.html

<!--- INDEX kotlinx.coroutines.channels -->

[kotlinx.coroutines.channels.produce]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/produce.html
[kotlinx.coroutines.channels.ReceiveChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/index.html
[kotlinx.coroutines.channels.ProducerScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-producer-scope/index.html
[kotlinx.coroutines.channels.Channel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-channel/index.html
[kotlinx.coroutines.channels.SendChannel.send]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/send.html
[kotlinx.coroutines.channels.ReceiveChannel.receive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/receive.html
[kotlinx.coroutines.channels.SendChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/index.html
[kotlinx.coroutines.channels.SendChannel.onSend]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/on-send.html
[kotlinx.coroutines.channels.SendChannel.trySend]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/try-send.html
[kotlinx.coroutines.channels.ReceiveChannel.onReceive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/on-receive.html
[kotlinx.coroutines.channels.ReceiveChannel.tryReceive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/try-receive.html
[kotlinx.coroutines.channels.receiveCatching]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/receive-catching.html
[kotlinx.coroutines.channels.onReceiveCatching]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/on-receive-catching.html

<!--- INDEX kotlinx.coroutines.selects -->

[kotlinx.coroutines.selects.select]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.selects/select.html
[kotlinx.coroutines.selects.SelectBuilder.onTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.selects/on-timeout.html

<!--- INDEX kotlinx.coroutines.test -->
<!--- END -->
