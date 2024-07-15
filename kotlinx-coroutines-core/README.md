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
 
| **Name**                                                                                            | **Description**
| --------------------------------------------------------------------------------------------------- | ---------------
| [Dispatchers.Main][kotlinx.coroutines.Dispatchers.Main]                                             | Confines coroutine execution to the UI thread
| [Dispatchers.Default][kotlinx.coroutines.Dispatchers.Default]                                       | Confines coroutine execution to a shared pool of background threads
| [Dispatchers.Unconfined][kotlinx.coroutines.Dispatchers.Unconfined]                                 | Does not confine coroutine execution in any way
| [CoroutineDispatcher.limitedParallelism][kotlinx.coroutines.CoroutineDispatcher.limitedParallelism] | Creates a view of the given dispatcher, limiting the number of tasks executing in parallel

More context elements:

| **Name**                                                                  | **Description**
| ------------------------------------------------------------------------- | ---------------
| [NonCancellable][kotlinx.coroutines.NonCancellable]                       | A non-cancelable job that is always active
| [CoroutineExceptionHandler][kotlinx.coroutines.CoroutineExceptionHandler] | Handler for uncaught exception

Synchronization primitives for coroutines:

| **Name**                                                                                                                                             | **Suspending functions**                                                                                            | **Description**
|------------------------------------------------------------------------------------------------------------------------------------------------------|---------------------------------------------------------------------------------------------------------------------| ---------------
| [Mutex][kotlinx.coroutines.sync.Mutex]                                                                                                               | [lock][kotlinx.coroutines.sync.Mutex.lock]                                                                          | Mutual exclusion
| [Semaphore][kotlinx.coroutines.sync.Semaphore]                                                                                                       | [acquire][kotlinx.coroutines.sync.Semaphore.acquire]                                                                | Limiting the maximum concurrency
| [Channel][kotlinx.coroutines.channels.Channel]                                                                                                       | [send][kotlinx.coroutines.channels.SendChannel.send], [receive][kotlinx.coroutines.channels.ReceiveChannel.receive] | Communication channel (aka queue or exchanger)
| [Flow](https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-flow/)                                         | [collect][kotlinx.coroutines.flow.Flow.collect]                                                                     | Asynchronous stream of values

<!---  Flow direct link is here to workaround MD case-insensitivity -->

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
helper function.
The [NonCancellable] job object is provided to suppress cancellation inside the
`withContext(NonCancellable) {...}` block of code.

Ways to construct asynchronous streams of values:

| **Name**                                                              | **Type** | **Description**
| --------------------------------------------------------------------- | -------- | ---------------
| [flow][kotlinx.coroutines.flow.flow]                                  | cold     | Runs a generator-style block of code that emits values
| [flowOf][kotlinx.coroutines.flow.flowOf]                              | cold     | Emits the values passed as arguments
| [channelFlow][kotlinx.coroutines.flow.channelFlow]                    | cold     | Runs the given code, providing a channel sending to which means emitting from the flow
| [callbackFlow][kotlinx.coroutines.flow.callbackFlow]                  | cold     | Allows transforming a callback-based API into a flow
| [ReceiveChannel.consumeAsFlow][kotlinx.coroutines.flow.consumeAsFlow] | hot      | Transforms a channel into a flow, emitting all of the received values to a single subscriber
| [ReceiveChannel.receiveAsFlow][kotlinx.coroutines.flow.receiveAsFlow] | hot      | Transforms a channel into a flow, distributing the received values among its subscribers
| [MutableSharedFlow][kotlinx.coroutines.flow.MutableSharedFlow]        | hot      | Allows emitting each value to arbitrarily many subscribers at once
| [MutableStateFlow][kotlinx.coroutines.flow.MutableStateFlow]          | hot      | Represents mutable state as a flow

A *cold* stream is some process of generating values, and this process is performed separately for each subscriber.
A *hot* stream uses the same source of values independently of whether there are subscribers.

A [select][kotlinx.coroutines.selects.select] expression waits for the result of multiple suspending functions simultaneously:

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

Synchronization primitives (mutex and semaphore).

# Package kotlinx.coroutines.channels

Channels &mdash; non-blocking primitives for communicating a stream of elements between coroutines.

# Package kotlinx.coroutines.flow

Flow &mdash; asynchronous cold and hot streams of elements.

# Package kotlinx.coroutines.selects

Select &mdash; expressions that perform multiple suspending operations simultaneously until one of them succeeds.

# Package kotlinx.coroutines.intrinsics

Low-level primitives for finer-grained control of coroutines.

# Package kotlinx.coroutines.future

[JDK 8's `CompletableFuture`](https://docs.oracle.com/javase/8/docs/api/java/util/concurrent/CompletableFuture.html) support.

# Package kotlinx.coroutines.stream

[JDK 8's `Stream`](https://docs.oracle.com/javase/8/docs/api/java/util/stream/Stream.html) support.

# Package kotlinx.coroutines.time

[JDK 8's `Duration`](https://docs.oracle.com/javase/8/docs/api/java/time/Duration.html) support via additional overloads for existing time-based operators.

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->

[kotlinx.coroutines.launch]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html
[kotlinx.coroutines.Job]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[kotlinx.coroutines.CoroutineScope]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[kotlinx.coroutines.async]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html
[kotlinx.coroutines.Deferred]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/index.html
[kotlinx.coroutines.runBlocking]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html
[CoroutineDispatcher]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
[kotlinx.coroutines.Dispatchers.Main]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-main.html
[kotlinx.coroutines.Dispatchers.Default]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html
[kotlinx.coroutines.Dispatchers.Unconfined]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-unconfined.html
[kotlinx.coroutines.CoroutineDispatcher.limitedParallelism]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/limited-parallelism.html
[kotlinx.coroutines.NonCancellable]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-non-cancellable/index.html
[kotlinx.coroutines.CoroutineExceptionHandler]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-exception-handler/index.html
[kotlinx.coroutines.delay]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html
[kotlinx.coroutines.yield]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/yield.html
[kotlinx.coroutines.withContext]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html
[kotlinx.coroutines.withTimeout]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout.html
[kotlinx.coroutines.withTimeoutOrNull]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout-or-null.html
[kotlinx.coroutines.awaitAll]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/await-all.html
[kotlinx.coroutines.joinAll]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/join-all.html
[suspendCancellableCoroutine]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/suspend-cancellable-coroutine.html
[NonCancellable]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-non-cancellable/index.html
[kotlinx.coroutines.Job.join]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/join.html
[kotlinx.coroutines.Job.onJoin]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/on-join.html
[kotlinx.coroutines.Job.isCompleted]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/is-completed.html
[kotlinx.coroutines.Deferred.await]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/await.html
[kotlinx.coroutines.Deferred.onAwait]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/on-await.html

<!--- INDEX kotlinx.coroutines.flow -->

[kotlinx.coroutines.flow.Flow.collect]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/collect.html
[kotlinx.coroutines.flow.flow]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flow.html
[kotlinx.coroutines.flow.flowOf]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/flow-of.html
[kotlinx.coroutines.flow.channelFlow]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/channel-flow.html
[kotlinx.coroutines.flow.callbackFlow]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/callback-flow.html
[kotlinx.coroutines.flow.consumeAsFlow]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/consume-as-flow.html
[kotlinx.coroutines.flow.receiveAsFlow]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/receive-as-flow.html
[kotlinx.coroutines.flow.MutableSharedFlow]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-mutable-shared-flow/index.html
[kotlinx.coroutines.flow.MutableStateFlow]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.flow/-mutable-state-flow/index.html

<!--- INDEX kotlinx.coroutines.sync -->

[kotlinx.coroutines.sync.Mutex]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/index.html
[kotlinx.coroutines.sync.Mutex.lock]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/lock.html
[kotlinx.coroutines.sync.Semaphore]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-semaphore/index.html
[kotlinx.coroutines.sync.Semaphore.acquire]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-semaphore/acquire.html

<!--- INDEX kotlinx.coroutines.channels -->

[kotlinx.coroutines.channels.produce]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/produce.html
[kotlinx.coroutines.channels.ReceiveChannel]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/index.html
[kotlinx.coroutines.channels.ProducerScope]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-producer-scope/index.html
[kotlinx.coroutines.channels.Channel]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-channel/index.html
[kotlinx.coroutines.channels.SendChannel.send]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/send.html
[kotlinx.coroutines.channels.ReceiveChannel.receive]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/receive.html
[kotlinx.coroutines.channels.SendChannel]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/index.html
[kotlinx.coroutines.channels.SendChannel.onSend]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/on-send.html
[kotlinx.coroutines.channels.SendChannel.trySend]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/try-send.html
[kotlinx.coroutines.channels.ReceiveChannel.onReceive]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/on-receive.html
[kotlinx.coroutines.channels.ReceiveChannel.tryReceive]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/try-receive.html
[kotlinx.coroutines.channels.receiveCatching]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/receive-catching.html
[kotlinx.coroutines.channels.onReceiveCatching]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/on-receive-catching.html

<!--- INDEX kotlinx.coroutines.selects -->

[kotlinx.coroutines.selects.select]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.selects/select.html
[kotlinx.coroutines.selects.SelectBuilder.onTimeout]: https://kotlinlang.org/api/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.selects/on-timeout.html

<!--- INDEX kotlinx.coroutines.test -->
<!--- END -->
