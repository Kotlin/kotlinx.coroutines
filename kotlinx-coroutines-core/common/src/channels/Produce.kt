package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlinx.coroutines.flow.*

/**
 * Scope for the [produce][CoroutineScope.produce], [callbackFlow] and [channelFlow] builders.
 */
public interface ProducerScope<in E> : CoroutineScope, SendChannel<E> {
    /**
     * A reference to the channel this coroutine [sends][send] elements to.
     * It is provided for convenience, so that the code in the coroutine can refer
     * to the channel as `channel` as opposed to `this`.
     * All the [SendChannel] functions on this interface delegate to
     * the channel instance returned by this property.
     */
    public val channel: SendChannel<E>
}

/**
 * Suspends the current coroutine until the channel is either
 * [closed][SendChannel.close] or [cancelled][ReceiveChannel.cancel].
 *
 * The given [block] will be executed unconditionally before this function returns.
 * `awaitClose { cleanup() }` is a convenient shorthand for the often useful form
 * `try { awaitClose() } finally { cleanup() }`.
 *
 * This function can only be invoked directly inside the same coroutine that is its receiver.
 * Specifying the receiver of [awaitClose] explicitly is most probably a mistake.
 *
 * This suspending function is cancellable: if the [Job] of the current coroutine is [cancelled][CoroutineScope.cancel]
 * while this suspending function is waiting, this function immediately resumes with [CancellationException].
 * There is a **prompt cancellation guarantee**: even if this function is ready to return, but was cancelled
 * while suspended, [CancellationException] will be thrown. See [suspendCancellableCoroutine] for low-level details.
 *
 * Example of usage:
 * ```
 * val callbackEventsStream = produce {
 *     val disposable = registerChannelInCallback(channel)
 *     awaitClose { disposable.dispose() }
 * }
 * ```
 *
 * Internally, [awaitClose] is implemented using [SendChannel.invokeOnClose].
 * Currently, every channel can have at most one [SendChannel.invokeOnClose] handler.
 * This means that calling [awaitClose] several times in a row or combining it with other [SendChannel.invokeOnClose]
 * invocations is prohibited.
 * An [IllegalStateException] will be thrown if this rule is broken.
 *
 * **Pitfall**: when used in [produce], if the channel is [cancelled][ReceiveChannel.cancel], [awaitClose] can either
 * return normally or throw a [CancellationException] due to a race condition.
 * The reason is that, for [produce], cancelling the channel and cancelling the coroutine of the [ProducerScope] is
 * done simultaneously.
 *
 * @throws IllegalStateException if invoked from outside the [ProducerScope] (by leaking `this` outside the producer
 * coroutine).
 * @throws IllegalStateException if this channel already has a [SendChannel.invokeOnClose] handler registered.
 */
public suspend fun ProducerScope<*>.awaitClose(block: () -> Unit = {}) {
    check(kotlin.coroutines.coroutineContext[Job] === this) { "awaitClose() can only be invoked from the producer context" }
    try {
        suspendCancellableCoroutine<Unit> { cont ->
            invokeOnClose {
                cont.resume(Unit)
            }
        }
    } finally {
        block()
    }
}

/**
 * Launches a new coroutine to produce a stream of values by sending them to a channel
 * and returns a reference to the coroutine as a [ReceiveChannel]. This resulting
 * object can be used to [receive][ReceiveChannel.receive] elements produced by this coroutine.
 *
 * The scope of the coroutine contains the [ProducerScope] interface, which implements
 * both [CoroutineScope] and [SendChannel], so that the coroutine can invoke [send][SendChannel.send] directly.
 *
 * The kind of the resulting channel depends on the specified [capacity] parameter.
 * See the [Channel] interface documentation for details.
 * By default, an unbuffered channel is created.
 *
 * ### Behavior on termination
 *
 * The channel is [closed][SendChannel.close] when the coroutine completes.
 *
 * ```
 * val values = listOf(1, 2, 3, 4)
 * val channel = produce<Int> {
 *     for (value in values) {
 *         send(value)
 *     }
 * }
 * check(channel.toList() == values)
 * ```
 *
 * The running coroutine is cancelled when the channel is [cancelled][ReceiveChannel.cancel].
 *
 * ```
 * val channel = produce<Int> {
 *     send(1)
 *     send(2)
 *     try {
 *         send(3) // will throw CancellationException
 *     } catch (e: CancellationException) {
 *         println("The channel was cancelled!)
 *         throw e // always rethrow CancellationException
 *     }
 * }
 * check(channel.receive() == 1)
 * check(channel.receive() == 2)
 * channel.cancel()
 * ```
 *
 * If this coroutine finishes with an exception, it will close the channel with that exception as the cause and
 * the resulting channel will become _failed_, so after receiving all the existing elements, all further attempts
 * to receive from it will throw the exception with which the coroutine finished.
 *
 * ```
 * val produceJob = Job()
 * // create and populate a channel with a buffer
 * val channel = produce<Int>(produceJob, capacity = Channel.UNLIMITED) {
 *     repeat(5) { send(it) }
 *     throw TestException()
 * }
 * produceJob.join() // wait for `produce` to fail
 * check(produceJob.isCancelled == true)
 * // prints 0, 1, 2, 3, 4, then throws `TestException`
 * for (value in channel) { println(value) }
 * ```
 *
 * When the coroutine is cancelled via structured concurrency and not the `cancel` function,
 * the channel does not automatically close until the coroutine completes,
 * so it is possible that some elements will be sent even after the coroutine is cancelled:
 *
 * ```
 * val parentScope = CoroutineScope(Dispatchers.Default)
 * val channel = parentScope.produce<Int>(capacity = Channel.UNLIMITED) {
 *     repeat(5) {
 *         send(it)
 *     }
 *     parentScope.cancel()
 *     // suspending after this point would fail, but sending succeeds
 *     send(-1)
 * }
 * for (c in channel) {
 *     println(c) // 0, 1, 2, 3, 4, -1
 * } // throws a `CancellationException` exception after reaching -1
 * ```
 *
 * Note that cancelling `produce` via structured concurrency closes the channel with a cause,
 * making it a _failed_ channel.
 *
 * The behavior around coroutine cancellation and error handling is experimental and may change in a future release.
 *
 * ### Coroutine context
 *
 * The coroutine context is inherited from this [CoroutineScope]. Additional context elements can be specified with the [context] argument.
 * If the context does not have any dispatcher or other [ContinuationInterceptor], then [Dispatchers.Default] is used.
 * The parent job is inherited from the [CoroutineScope] as well, but it can also be overridden
 * with a corresponding [context] element.
 *
 * See [newCoroutineContext] for a description of debugging facilities available for newly created coroutines.
 *
 * ### Undelivered elements
 *
 * Some values that [produce] creates may be lost:
 *
 * ```
 * val channel = produce(Dispatchers.Default, capacity = 5) {
 *     repeat(100) {
 *         send(it)
 *         println("Sent $it")
 *     }
 * }
 * channel.cancel() // no elements can be received after this!
 * ```
 *
 * There is no way to recover these lost elements.
 * If this is unsuitable, please create a [Channel] manually and pass the `onUndeliveredElement` callback to the
 * constructor: [Channel(onUndeliveredElement = ...)][Channel].
 *
 * ### Usage example
 *
 * ```
 * /* Generate random integers until we find the square root of 9801.
 *    To calculate whether the given number is that square root,
 *    use several coroutines that separately process these integers.
 *    Alternatively, we may randomly give up during value generation.
 *    `produce` is used to generate the integers and put them into a
 *    channel, from which the square-computing coroutines take them. */
 * val parentScope = CoroutineScope(SupervisorJob())
 * val channel = parentScope.produce<Int>(
 *     Dispatchers.IO,
 *     capacity = 16 // buffer of size 16
 * ) {
 *     // this code will run on Dispatchers.IO
 *     while (true) {
 *         val request = run {
 *             // simulate waiting for the next request
 *             delay(5.milliseconds)
 *             val randomInt = Random.nextInt(-1, 100)
 *             if (randomInt == -1) {
 *                 // external termination request received
 *                 println("Producer: no longer accepting requests")
 *                 return@produce
 *             }
 *             println("Producer: sending a request ($randomInt)")
 *             randomInt
 *         }
 *         send(request)
 *     }
 * }
 * // Launch consumers
 * repeat(4) {
 *     launch(Dispatchers.Default) {
 *         for (request in channel) {
 *             // simulate processing a request
 *             delay(25.milliseconds)
 *             println("Consumer $it: received a request ($request)")
 *             if (request * request == 9801) {
 *                 println("Consumer $it found the square root of 9801!")
 *                 /* the work is done, the producer may finish.
 *                    the internal termination request will cancel
 *                    the producer on the next suspension point. */
 *                 channel.cancel()
 *             }
 *         }
 *     }
 * }
 * ```
 *
 * **Note: This is an experimental api.** Behaviour of producers that work as children in a parent scope with respect
 *        to cancellation and error handling may change in the future.
 */
@ExperimentalCoroutinesApi
public fun <E> CoroutineScope.produce(
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = Channel.RENDEZVOUS,
    @BuilderInference block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> =
    produce(context, capacity, BufferOverflow.SUSPEND, CoroutineStart.DEFAULT, onCompletion = null, block = block)

/**
 * **This is an internal API and should not be used from general code.**
 * The `onCompletion` parameter will be redesigned.
 * If you have to use the `onCompletion` operator, please report to https://github.com/Kotlin/kotlinx.coroutines/issues/.
 * As a temporary solution, [invokeOnCompletion][Job.invokeOnCompletion] can be used instead:
 * ```
 * fun <E> ReceiveChannel<E>.myOperator(): ReceiveChannel<E> = GlobalScope.produce(Dispatchers.Unconfined) {
 *     coroutineContext[Job]?.invokeOnCompletion { consumes() }
 * }
 * ```
 * @suppress
 */
@InternalCoroutinesApi
public fun <E> CoroutineScope.produce(
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = 0,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    @BuilderInference block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> =
    produce(context, capacity, BufferOverflow.SUSPEND, start, onCompletion, block)

// Internal version of produce that is maximally flexible, but is not exposed through public API (too many params)
internal fun <E> CoroutineScope.produce(
    context: CoroutineContext = EmptyCoroutineContext,
    capacity: Int = 0,
    onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    onCompletion: CompletionHandler? = null,
    @BuilderInference block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> {
    val channel = Channel<E>(capacity, onBufferOverflow)
    val newContext = newCoroutineContext(context)
    val coroutine = ProducerCoroutine(newContext, channel)
    if (onCompletion != null) coroutine.invokeOnCompletion(handler = onCompletion)
    coroutine.start(start, coroutine, block)
    return coroutine
}

private class ProducerCoroutine<E>(
    parentContext: CoroutineContext, channel: Channel<E>
) : ChannelCoroutine<E>(parentContext, channel, true, active = true), ProducerScope<E> {
    override val isActive: Boolean
        get() = super.isActive

    override fun onCompleted(value: Unit) {
        _channel.close()
    }

    override fun onCancelled(cause: Throwable, handled: Boolean) {
        val processed = _channel.close(cause)
        if (!processed && !handled) handleCoroutineException(context, cause)
    }
}
