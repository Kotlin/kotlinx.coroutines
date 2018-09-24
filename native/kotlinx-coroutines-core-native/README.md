# Module kotlinx-coroutines-core-native

Core primitives to work with coroutines on Kotlin/Native.

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
| [Dispatchers.Default]       | References current [runBlocking] event loop
| [Dispatchers.Unconfined]    | Does not confine coroutine execution in any way

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
`run(NonCancellable) {...}` block of code.

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
<!--- END -->
