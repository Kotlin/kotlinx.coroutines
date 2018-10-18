# Module kotlinx-coroutines-core-native

Core primitives to work with coroutines on Kotlin/Native.

Coroutine builder functions:

| **Name**      | **Result**    | **Scope**        | **Description**
| ------------- | ------------- | ---------------- | ---------------
| [launch]      | [Job]         | [CoroutineScope] | Launches coroutine that does not have any result 
| [async]       | [Deferred]    | [CoroutineScope] | Returns a single value with the future result
| [produce][kotlinx.coroutines.channels.produce]     | [ReceiveChannel][kotlinx.coroutines.channels.ReceiveChannel] | [ProducerScope][kotlinx.coroutines.channels.ProducerScope]  | Produces a stream of elements
| [actor][kotlinx.coroutines.channels.actor]     | [SendChannel][kotlinx.coroutines.channels.SendChannel] | [ActorScope][kotlinx.coroutines.channels.ActorScope]  | Processes a stream of messages
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
`run(NonCancellable) {...}` block of code.

[Select][kotlinx.coroutines.selects.select] expression waits for the result of multiple suspending functions simultaneously:

| **Receiver**     | **Suspending function**                       | **Select clause**                                | **Non-suspending version**
| ---------------- | --------------------------------------------- | ------------------------------------------------ | --------------------------
| [Job]            | [join][Job.join]                              | [onJoin][Job.onJoin]                   | [isCompleted][Job.isCompleted]
| [Deferred]       | [await][Deferred.await]                       | [onAwait][Deferred.onAwait]                 | [isCompleted][Job.isCompleted]
| [SendChannel][kotlinx.coroutines.channels.SendChannel]    | [send][kotlinx.coroutines.channels.SendChannel.send]                      | [onSend][kotlinx.coroutines.channels.SendChannel.onSend]                   | [offer][kotlinx.coroutines.channels.SendChannel.offer]
| [ReceiveChannel][kotlinx.coroutines.channels.ReceiveChannel] | [receive][kotlinx.coroutines.channels.ReceiveChannel.receive]             | [onReceive][kotlinx.coroutines.channels.ReceiveChannel.onReceive]             | [poll][kotlinx.coroutines.channels.ReceiveChannel.poll]
| [ReceiveChannel][kotlinx.coroutines.channels.ReceiveChannel] | [receiveOrNull][kotlinx.coroutines.channels.ReceiveChannel.receiveOrNull] | [onReceiveOrNull][kotlinx.coroutines.channels.ReceiveChannel.onReceiveOrNull] | [poll][kotlinx.coroutines.channels.ReceiveChannel.poll]
| [Mutex][kotlinx.coroutines.sync.Mutex]          | [lock][kotlinx.coroutines.sync.Mutex.lock]                            | [onLock][kotlinx.coroutines.sync.Mutex.onLock]                   | [tryLock][kotlinx.coroutines.sync.Mutex.tryLock]
| none            | [delay]                                        | [onTimeout][kotlinx.coroutines.selects.SelectBuilder.onTimeout]                   | none

<!--- MODULE kotlinx-coroutines-core -->
<!--- INDEX kotlinx.coroutines -->
[launch]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/launch.html
[Job]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/index.html
[CoroutineScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-scope/index.html
[async]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/async.html
[Deferred]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/index.html
[runBlocking]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/run-blocking.html
[CoroutineDispatcher]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-dispatcher/index.html
[Dispatchers.Default]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-default.html
[Dispatchers.Unconfined]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-dispatchers/-unconfined.html
[NonCancellable]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-non-cancellable.html
[CoroutineExceptionHandler]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-coroutine-exception-handler/index.html
[delay]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/delay.html
[yield]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/yield.html
[withContext]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-context.html
[withTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout.html
[withTimeoutOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/with-timeout-or-null.html
[awaitAll]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/await-all.html
[joinAll]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/join-all.html
[suspendCancellableCoroutine]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/suspend-cancellable-coroutine.html
[Job.join]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/join.html
[Job.onJoin]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/on-join.html
[Job.isCompleted]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-job/is-completed.html
[Deferred.await]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/await.html
[Deferred.onAwait]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines/-deferred/on-await.html
<!--- INDEX kotlinx.coroutines.sync -->
[kotlinx.coroutines.sync.Mutex]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/index.html
[kotlinx.coroutines.sync.Mutex.lock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/lock.html
[kotlinx.coroutines.sync.Mutex.onLock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/on-lock.html
[kotlinx.coroutines.sync.Mutex.tryLock]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.sync/-mutex/try-lock.html
<!--- INDEX kotlinx.coroutines.channels -->
[kotlinx.coroutines.channels.produce]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/produce.html
[kotlinx.coroutines.channels.ReceiveChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/index.html
[kotlinx.coroutines.channels.ProducerScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-producer-scope/index.html
[kotlinx.coroutines.channels.actor]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/actor.html
[kotlinx.coroutines.channels.SendChannel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/index.html
[kotlinx.coroutines.channels.ActorScope]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-actor-scope/index.html
[kotlinx.coroutines.channels.Channel]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-channel/index.html
[kotlinx.coroutines.channels.SendChannel.send]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/send.html
[kotlinx.coroutines.channels.ReceiveChannel.receive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/receive.html
[kotlinx.coroutines.channels.SendChannel.onSend]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/on-send.html
[kotlinx.coroutines.channels.SendChannel.offer]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-send-channel/offer.html
[kotlinx.coroutines.channels.ReceiveChannel.onReceive]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/on-receive.html
[kotlinx.coroutines.channels.ReceiveChannel.poll]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/poll.html
[kotlinx.coroutines.channels.ReceiveChannel.receiveOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/receive-or-null.html
[kotlinx.coroutines.channels.ReceiveChannel.onReceiveOrNull]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.channels/-receive-channel/on-receive-or-null.html
<!--- INDEX kotlinx.coroutines.selects -->
[kotlinx.coroutines.selects.select]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.selects/select.html
[kotlinx.coroutines.selects.SelectBuilder.onTimeout]: https://kotlin.github.io/kotlinx.coroutines/kotlinx-coroutines-core/kotlinx.coroutines.selects/-select-builder/on-timeout.html
<!--- END -->
