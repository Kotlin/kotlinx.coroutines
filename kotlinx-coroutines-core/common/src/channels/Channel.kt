package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.Channel.Factory.BUFFERED
import kotlinx.coroutines.channels.Channel.Factory.CHANNEL_DEFAULT_CAPACITY
import kotlinx.coroutines.channels.Channel.Factory.CONFLATED
import kotlinx.coroutines.channels.Channel.Factory.RENDEZVOUS
import kotlinx.coroutines.channels.Channel.Factory.UNLIMITED
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlin.contracts.*
import kotlin.internal.*
import kotlin.jvm.*

/**
 * Sender's interface to a [Channel].
 *
 * Combined, [SendChannel] and [ReceiveChannel] define the complete [Channel] interface.
 *
 * It is not expected that this interface will be implemented directly.
 * Instead, the existing [Channel] implementations can be used or delegated to.
 */
public interface SendChannel<in E> {
    /**
     * Returns `true` if this channel was closed by an invocation of [close] or its receiving side was [cancelled][ReceiveChannel.cancel].
     * This means that calling [send] will result in an exception.
     *
     * Note that if this property returns `false`, it does not guarantee that a subsequent call to [send] will succeed,
     * as the channel can be concurrently closed right after the check.
     * For such scenarios, [trySend] is the more robust solution: it attempts to send the element and returns
     * a result that says whether the channel was closed, and if not, whether sending a value was successful.
     *
     * ```
     * // DANGER! THIS CHECK IS NOT RELIABLE!
     * if (!channel.isClosedForSend) {
     *     channel.send(element) // can still fail!
     * } else {
     *     println("Can not send: the channel is closed")
     * }
     * // DO THIS INSTEAD:
     * channel.trySend(element).onClosed {
     *     println("Can not send: the channel is closed")
     * }
     * ```
     *
     * The primary intended usage of this property is skipping some portions of code that should not be executed if the
     * channel is already known to be closed.
     * For example:
     *
     * ```
     * if (channel.isClosedForSend) {
     *    // fast path
     *    return
     * } else {
     *    // slow path: actually computing the value
     *    val nextElement = run {
     *        // some heavy computation
     *    }
     *    channel.send(nextElement) // can fail anyway,
     *    // but at least we tried to avoid the computation
     * }
     * ```
     *
     * However, in many cases, even that can be achieved more idiomatically by cancelling the coroutine producing the
     * elements to send.
     * See [produce] for a way to launch a coroutine that produces elements and cancels itself when the channel is
     * closed.
     *
     * [isClosedForSend] can also be used for assertions and diagnostics to verify the expected state of the channel.
     *
     * @see SendChannel.trySend
     * @see SendChannel.close
     * @see ReceiveChannel.cancel
     */
    @DelicateCoroutinesApi
    public val isClosedForSend: Boolean

    /**
     * Sends the specified [element] to this channel.
     *
     * This function suspends if it does not manage to pass the element to the channel's buffer
     * (or directly the receiving side if there's no buffer),
     * and it can be cancelled with or without having successfully passed the element.
     * See the "Suspending and cancellation" section below for details.
     * If the channel is [closed][close], an exception is thrown (see below).
     *
     * ```
     * val channel = Channel<Int>()
     * launch {
     *     check(channel.receive() == 5)
     * }
     * channel.send(5) // suspends until 5 is received
     * ```
     *
     * ## Suspending and cancellation
     *
     * If the [BufferOverflow] strategy of this channel is [BufferOverflow.SUSPEND],
     * this function may suspend.
     * The exact scenarios differ depending on the channel's capacity:
     * - If the channel is [rendezvous][RENDEZVOUS],
     *   the sender will be suspended until the receiver calls [ReceiveChannel.receive].
     * - If the channel is [unlimited][UNLIMITED] or [conflated][CONFLATED],
     *   the sender will never be suspended even with the [BufferOverflow.SUSPEND] strategy.
     * - If the channel is buffered (either [BUFFERED] or uses a non-default buffer capacity),
     *   the sender will be suspended until the buffer has free space.
     *
     * This suspending function is cancellable: if the [Job] of the current coroutine is cancelled while this
     * suspending function is waiting, this function immediately resumes with [CancellationException].
     * There is a **prompt cancellation guarantee**: even if [send] managed to send the element, but was cancelled
     * while suspended, [CancellationException] will be thrown. See [suspendCancellableCoroutine] for low-level details.
     *
     * Because of the prompt cancellation guarantee, an exception does not always mean a failure to deliver the element.
     * See the "Undelivered elements" section in the [Channel] documentation
     * for details on handling undelivered elements.
     *
     * Note that this function does not check for cancellation when it is not suspended.
     * Use [ensureActive] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed:
     *
     * ```
     * // because of UNLIMITED, sending to this channel never suspends
     * val channel = Channel<Int>(Channel.UNLIMITED)
     * val job = launch {
     *     while (isActive) {
     *         channel.send(42)
     *     }
     *     // the loop exits when the job is cancelled
     * }
     * ```
     *
     * This isn't needed if other cancellable functions are called inside the loop, like [delay].
     *
     * ## Sending to a closed channel
     *
     * If a channel was [closed][close] before [send] was called and no cause was specified,
     * an [ClosedSendChannelException] will be thrown from [send].
     * If a channel was [closed][close] with a cause before [send] was called,
     * then [send] will rethrow the same (in the `===` sense) exception that was passed to [close].
     *
     * In both cases, it is guaranteed that the element was not delivered to the consumer,
     * and the `onUndeliveredElement` callback will be called.
     * See the "Undelivered elements" section in the [Channel] documentation
     * for details on handling undelivered elements.
     *
     * [Closing][close] a channel _after_ this function suspends does not cause this suspended [send] invocation
     * to abort: although subsequent invocations of [send] fail, the existing ones will continue to completion,
     * unless the sending coroutine is cancelled.
     *
     * ## Related
     *
     * This function can be used in [select] invocations with the [onSend] clause.
     * Use [trySend] to try sending to this channel without waiting and throwing.
     */
    public suspend fun send(element: E)

    /**
     * Clause for the [select] expression of the [send] suspending function that selects when the element that is
     * specified as the parameter is sent to the channel.
     * When the clause is selected, the reference to this channel is passed into the corresponding block.
     *
     * The [select] invocation fails with an exception if the channel [is closed for `send`][isClosedForSend] before
     * the [select] suspends (see the "Sending to a closed channel" section of [send]).
     *
     * Example:
     * ```
     * val sendChannels = List(4) { index ->
     *     Channel<Int>(onUndeliveredElement = {
     *         println("Undelivered element $it for $index")
     *     }).also { channel ->
     *         // launch a consumer for this channel
     *         launch {
     *             withTimeout(1.seconds) {
     *                 println("Consumer $index receives: ${channel.receive()}")
     *             }
     *         }
     *     }
     * }
     * val element = 42
     * select {
     *     for (channel in sendChannels) {
     *         channel.onSend(element) {
     *             println("Sent to channel $it")
     *         }
     *     }
     * }
     * ```
     * Here, we start a [select] expression that waits for exactly one of the four [onSend] invocations
     * to successfully send the element to the receiver,
     * and the other three will instead invoke the `onUndeliveredElement` callback.
     * See the "Undelivered elements" section in the [Channel] documentation
     * for details on handling undelivered elements.
     *
     * Like [send], [onSend] obeys the rules of prompt cancellation:
     * [select] may finish with a [CancellationException] even if the element was successfully sent.
     */
    public val onSend: SelectClause2<E, SendChannel<E>>

    /**
     * Attempts to add the specified [element] to this channel without waiting.
     *
     * [trySend] never suspends and never throws exceptions.
     * Instead, it returns a [ChannelResult] that encapsulates the result of the operation.
     * This makes it different from [send], which can suspend and throw exceptions.
     *
     * If this channel is currently full and cannot receive new elements at the time or is [closed][close],
     * this function returns a result that indicates [a failure][ChannelResult.isFailure].
     * In this case, it is guaranteed that the element was not delivered to the consumer and the
     * `onUndeliveredElement` callback, if one is provided during the [Channel]'s construction, does *not* get called.
     *
     * [trySend] can be used as a non-`suspend` alternative to [send] in cases where it's known beforehand
     * that the channel's buffer can not overflow.
     * ```
     * class Coordinates(val x: Int, val y: Int)
     * // A channel for a single subscriber that stores the latest mouse position update.
     * // If more than one subscriber is expected, consider using a `StateFlow` instead.
     * val mousePositionUpdates = Channel<Coordinates>(Channel.CONFLATED)
     * // Notifies the subscriber about the new mouse position.
     * // If the subscriber is slow, the intermediate updates are dropped.
     * fun moveMouse(coordinates: Coordinates) {
     *     val result = mousePositionUpdates.trySend(coordinates)
     *     if (result.isClosed) {
     *         error("Mouse position is no longer being processed")
     *     }
     * }
     * ```
     */
    public fun trySend(element: E): ChannelResult<Unit>

    /**
     * Closes this channel so that subsequent attempts to [send] to it fail.
     *
     * Returns `true` if the channel was not closed previously and the call to this function closed it.
     * If the channel was already closed, this function does nothing and returns `false`.
     *
     * The existing elements in the channel remain there, and likewise,
     * the calls to [send] an [onSend] that have suspended before [close] was called will not be affected.
     * Only the subsequent calls to [send], [trySend], or [onSend] will fail.
     * [isClosedForSend] will start returning `true` immediately after this function is called.
     *
     * Once all the existing elements are received, the channel will be considered closed for `receive` as well.
     * This means that [receive][ReceiveChannel.receive] will also start throwing exceptions.
     * At that point, [isClosedForReceive][ReceiveChannel.isClosedForReceive] will start returning `true`.
     *
     * If the [cause] is non-null, it will be thrown from all the subsequent attempts to [send] to this channel,
     * as well as from all the attempts to [receive][ReceiveChannel.receive] from the channel after no elements remain.
     *
     * If the [cause] is null, the channel is considered to have completed normally.
     * All subsequent calls to [send] will throw a [ClosedSendChannelException],
     * whereas calling [receive][ReceiveChannel.receive] will throw a [ClosedReceiveChannelException]
     * after there are no more elements.
     *
     * ```
     * val channel = Channel<Int>()
     * channel.send(1)
     * channel.close()
     * try {
     *     channel.send(2)
     *     error("The channel is closed, so this line is never reached")
     * } catch (e: ClosedSendChannelException) {
     *     // expected
     * }
     * ```
     */
    public fun close(cause: Throwable? = null): Boolean

    /**
     * Registers a [handler] that is synchronously invoked once the channel is [closed][close]
     * or the receiving side of this channel is [cancelled][ReceiveChannel.cancel].
     * Only one handler can be attached to a channel during its lifetime.
     * The `handler` is invoked when [isClosedForSend] starts to return `true`.
     * If the channel is closed already, the handler is invoked immediately.
     *
     * The meaning of `cause` that is passed to the handler:
     * - `null` if the channel was [closed][close] normally with `cause = null`.
     * - Instance of [CancellationException] if the channel was [cancelled][ReceiveChannel.cancel] normally
     *   without the corresponding argument.
     * - The cause of `close` or `cancel` otherwise.
     *
     * ### Execution context and exception safety
     *
     * The [handler] is executed as part of the closing or cancelling operation,
     * and only after the channel reaches its final state.
     * This means that if the handler throws an exception or hangs,
     * the channel will still be successfully closed or cancelled.
     * Unhandled exceptions from [handler] are propagated to the closing or cancelling operation's caller.
     *
     * Example of usage:
     * ```
     * val events = Channel<Event>(Channel.UNLIMITED)
     * callbackBasedApi.registerCallback { event ->
     *     events.trySend(event)
     *         .onClosed { /* channel is already closed, but the callback hasn't stopped yet */ }
     * }
     *
     * val uiUpdater = uiScope.launch(Dispatchers.Main) {
     *     events.consume { /* handle events */ }
     * }
     * // Stop the callback after the channel is closed or cancelled
     * events.invokeOnClose { callbackBasedApi.stop() }
     * ```
     *
     * **Stability note.** This function constitutes a stable API surface, with the only exception being
     * that an [IllegalStateException] is thrown when multiple handlers are registered.
     * This restriction could be lifted in the future.
     *
     * @throws UnsupportedOperationException if the underlying channel does not support [invokeOnClose].
     * Implementation note: currently, [invokeOnClose] is unsupported only by Rx-like integrations.
     *
     * @throws IllegalStateException if another handler was already registered
     */
    public fun invokeOnClose(handler: (cause: Throwable?) -> Unit)

    /**
     * **Deprecated** offer method.
     *
     * This method was deprecated in the favour of [trySend].
     * It has proven itself as the most error-prone method in Channel API:
     *
     * - `Boolean` return type creates the false sense of security, implying that `false`
     *   is returned instead of throwing an exception.
     * - It was used mostly from non-suspending APIs where CancellationException triggered
     *   internal failures in the application (the most common source of bugs).
     * - Due to signature and explicit `if (ch.offer(...))` checks it was easy to
     *   oversee such error during code review.
     * - Its name was not aligned with the rest of the API and tried to mimic Java's queue instead.
     *
     * **NB** Automatic migration provides best-effort for the user experience, but requires removal
     * or adjusting of the code that relied on the exception handling.
     * The complete replacement has a more verbose form:
     * ```
     * channel.trySend(element)
     *     .onClosed { throw it ?: ClosedSendChannelException("Channel was closed normally") }
     *     .isSuccess
     * ```
     *
     * See https://github.com/Kotlin/kotlinx.coroutines/issues/974 for more context.
     *
     * @suppress **Deprecated**.
     */
    @Deprecated(
        level = DeprecationLevel.ERROR,
        message = "Deprecated in the favour of 'trySend' method",
        replaceWith = ReplaceWith("trySend(element).isSuccess")
    ) // Warning since 1.5.0, error since 1.6.0, not hidden until 1.8+ because API is quite widespread
    public fun offer(element: E): Boolean {
        val result = trySend(element)
        if (result.isSuccess) return true
        throw recoverStackTrace(result.exceptionOrNull() ?: return false)
    }
}

/**
 * Receiver's interface to a [Channel].
 *
 * Combined, [SendChannel] and [ReceiveChannel] define the complete [Channel] interface.
 */
public interface ReceiveChannel<out E> {
    /**
     * Returns `true` if the sending side of this channel was [closed][SendChannel.close]
     * and all previously sent items were already received (which also happens for [cancelled][cancel] channels).
     *
     * Note that if this property returns `false`,
     * it does not guarantee that a subsequent call to [receive] will succeed,
     * as the channel can be concurrently cancelled or closed right after the check.
     * For such scenarios, [receiveCatching] is the more robust solution:
     * if the channel is closed, instead of throwing an exception, [receiveCatching] returns a result that allows
     * querying it.
     *
     * ```
     * // DANGER! THIS CHECK IS NOT RELIABLE!
     * if (!channel.isClosedForReceive) {
     *     channel.receive() // can still fail!
     * } else {
     *     println("Can not receive: the channel is closed")
     *     null
     * }
     * // DO THIS INSTEAD:
     * channel.receiveCatching().onClosed {
     *     println("Can not receive: the channel is closed")
     * }.getOrNull()
     * ```
     *
     * The primary intended usage of this property is for assertions and diagnostics to verify the expected state of
     * the channel.
     * Using it in production code is discouraged.
     *
     * @see ReceiveChannel.receiveCatching
     * @see ReceiveChannel.cancel
     * @see SendChannel.close
     */
    @DelicateCoroutinesApi
    public val isClosedForReceive: Boolean

    /**
     * Returns `true` if the channel contains no elements and isn't [closed for `receive`][isClosedForReceive].
     *
     * If [isEmpty] returns `true`, it means that calling [receive] at exactly the same moment would suspend.
     * However, calling [receive] immediately after checking [isEmpty] may or may not suspend, as new elements
     * could have been added or removed or the channel could have been closed for `receive` between the two invocations.
     * Consider using [tryReceive] in cases when suspensions are undesirable:
     *
     * ```
     * // DANGER! THIS CHECK IS NOT RELIABLE!
     * while (!channel.isEmpty) {
     *     // can still suspend if other `receive` happens in parallel!
     *     val element = channel.receive()
     *     println(element)
     * }
     * // DO THIS INSTEAD:
     * while (true) {
     *     val element = channel.tryReceive().getOrNull() ?: break
     *     println(element)
     * }
     * ```
     */
    @ExperimentalCoroutinesApi
    public val isEmpty: Boolean

    /**
     * Retrieves an element, removing it from the channel.
     *
     * This function suspends if the channel is empty, waiting until an element is available.
     * If the channel is [closed for `receive`][isClosedForReceive], an exception is thrown (see below).
     * ```
     * val channel = Channel<Int>()
     * launch {
     *     val element = channel.receive() // suspends until 5 is available
     *     check(element == 5)
     * }
     * channel.send(5)
     * ```
     *
     * ## Suspending and cancellation
     *
     * This suspending function is cancellable: if the [Job] of the current coroutine is cancelled while this
     * suspending function is waiting, this function immediately resumes with [CancellationException].
     * There is a **prompt cancellation guarantee**: even if [receive] managed to retrieve the element from the channel,
     * but was cancelled while suspended, [CancellationException] will be thrown, and, if
     * the channel has an `onUndeliveredElement` callback installed, the retrieved element will be passed to it.
     * See the "Undelivered elements" section in the [Channel] documentation
     * for details on handling undelivered elements.
     * See [suspendCancellableCoroutine] for the low-level details of prompt cancellation.
     *
     * Note that this function does not check for cancellation when it manages to immediately receive an element without
     * suspending.
     * Use [ensureActive] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed:
     *
     * ```
     * val channel = Channel<Int>()
     * launch { // a very fast producer
     *     while (true) {
     *         channel.send(42)
     *     }
     * }
     * val consumer = launch { // a slow consumer
     *     while (isActive) {
     *         val element = channel.receive()
     *         // some slow computation involving `element`
     *     }
     * }
     * delay(100.milliseconds)
     * consumer.cancelAndJoin()
     * ```
     *
     * ## Receiving from a closed channel
     *
     * - Attempting to [receive] from a [closed][SendChannel.close] channel while there are still some elements
     *   will successfully retrieve an element from the channel.
     * - When a channel is [closed][SendChannel.close] and there are no elements remaining,
     *   the channel becomes [closed for `receive`][isClosedForReceive].
     *   After that,
     *   [receive] will rethrow the same (in the `===` sense) exception that was passed to [SendChannel.close],
     *   or [ClosedReceiveChannelException] if none was given.
     *
     * ## Related
     *
     * This function can be used in [select] invocations with the [onReceive] clause.
     * Use [tryReceive] to try receiving from this channel without waiting and throwing.
     * Use [receiveCatching] to receive from this channel without throwing.
     */
    public suspend fun receive(): E

    /**
     * Clause for the [select] expression of the [receive] suspending function that selects with the element
     * received from the channel.
     *
     * The [select] invocation fails with an exception if the channel [is closed for `receive`][isClosedForReceive]
     * at any point, even if other [select] clauses could still work.
     *
     * Example:
     * ```
     * class ScreenSize(val width: Int, val height: Int)
     * class MouseClick(val x: Int, val y: Int)
     * val screenResizes = Channel<ScreenSize>(Channel.CONFLATED)
     * val mouseClicks = Channel<MouseClick>(Channel.CONFLATED)
     *
     * launch(Dispatchers.Main) {
     *     while (true) {
     *         select {
     *             screenResizes.onReceive { newSize ->
     *                 // update the UI to the new screen size
     *             }
     *             mouseClicks.onReceive { click ->
     *                 // react to a mouse click
     *             }
     *         }
     *     }
     * }
     * ```
     *
     * Like [receive], [onReceive] obeys the rules of prompt cancellation:
     * [select] may finish with a [CancellationException] even if an element was successfully retrieved,
     * in which case the `onUndeliveredElement` callback will be called.
     */
    public val onReceive: SelectClause1<E>

    /**
     * Retrieves an element, removing it from the channel.
     *
     * A difference from [receive] is that this function encapsulates a failure in its return value instead of throwing
     * an exception.
     * However, it will still throw [CancellationException] if the coroutine calling [receiveCatching] is cancelled.
     *
     * It is guaranteed that the only way this function can return a [failed][ChannelResult.isFailure] result is when
     * the channel is [closed for `receive`][isClosedForReceive], so [ChannelResult.isClosed] is also true.
     *
     * This function suspends if the channel is empty, waiting until an element is available or the channel becomes
     * closed.
     * ```
     * val channel = Channel<Int>()
     * launch {
     *     while (true) {
     *         val result = channel.receiveCatching() // suspends
     *         when (val element = result.getOrNull()) {
     *             null -> break // the channel is closed
     *             else -> check(element == 5)
     *         }
     *     }
     * }
     * channel.send(5)
     * ```
     *
     * ## Suspending and cancellation
     *
     * This suspending function is cancellable: if the [Job] of the current coroutine is cancelled while this
     * suspending function is waiting, this function immediately resumes with [CancellationException].
     * There is a **prompt cancellation guarantee**: even if [receiveCatching] managed to retrieve the element from the
     * channel, but was cancelled while suspended, [CancellationException] will be thrown, and, if
     * the channel has an `onUndeliveredElement` callback installed, the retrieved element will be passed to it.
     * See the "Undelivered elements" section in the [Channel] documentation
     * for details on handling undelivered elements.
     * See [suspendCancellableCoroutine] for the low-level details of prompt cancellation.
     *
     * Note that this function does not check for cancellation when it manages to immediately receive an element without
     * suspending.
     * Use [ensureActive] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed:
     *
     * ```
     * val channel = Channel<Int>()
     * launch { // a very fast producer
     *     while (true) {
     *         channel.send(42)
     *     }
     * }
     * val consumer = launch { // a slow consumer
     *     while (isActive) {
     *         val element = channel.receiveCatching().getOrNull() ?: break
     *         // some slow computation involving `element`
     *     }
     * }
     * delay(100.milliseconds)
     * consumer.cancelAndJoin()
     * ```
     *
     * ## Receiving from a closed channel
     *
     * - Attempting to [receiveCatching] from a [closed][SendChannel.close] channel while there are still some elements
     *   will successfully retrieve an element from the channel.
     * - When a channel is [closed][SendChannel.close] and there are no elements remaining,
     *   the channel becomes [closed for `receive`][isClosedForReceive].
     *   After that, [receiveCatching] will return a result with [ChannelResult.isClosed] set.
     *   [ChannelResult.exceptionOrNull] will be the exact (in the `===` sense) exception
     *   that was passed to [SendChannel.close],
     *   or `null` if none was given.
     *
     * ## Related
     *
     * This function can be used in [select] invocations with the [onReceiveCatching] clause.
     * Use [tryReceive] to try receiving from this channel without waiting and throwing.
     * Use [receive] to receive from this channel and throw exceptions on error.
     */
    public suspend fun receiveCatching(): ChannelResult<E>

    /**
     * Clause for the [select] expression of the [receiveCatching] suspending function that selects
     * with a [ChannelResult] when an element is retrieved or the channel gets closed.
     *
     * Like [receiveCatching], [onReceiveCatching] obeys the rules of prompt cancellation:
     * [select] may finish with a [CancellationException] even if an element was successfully retrieved,
     * in which case the `onUndeliveredElement` callback will be called.
     */
    // TODO: think of an example of when this could be useful
    public val onReceiveCatching: SelectClause1<ChannelResult<E>>

    /**
     * Attempts to retrieve an element without waiting, removing it from the channel.
     *
     * - When the channel is non-empty, a [successful][ChannelResult.isSuccess] result is returned,
     *   and [ChannelResult.getOrNull] returns the retrieved element.
     * - When the channel is empty, a [failed][ChannelResult.isFailure] result is returned.
     * - When the channel is already [closed for `receive`][isClosedForReceive],
     *   returns the ["channel is closed"][ChannelResult.isClosed] result.
     *   If the channel was [closed][SendChannel.close] with a cause (for example, [cancelled][cancel]),
     *   [ChannelResult.exceptionOrNull] contains the cause.
     *
     * This function is useful when implementing on-demand allocation of resources to be stored in the channel:
     *
     * ```
     * val resourcePool = Channel<Resource>(maxResources)
     *
     * suspend fun withResource(block: (Resource) -> Unit) {
     *     val result = resourcePool.tryReceive()
     *     val resource = result.getOrNull()
     *         ?: tryCreateNewResource() // try to create a new resource
     *         ?: resourcePool.receive() // could not create: actually wait for the resource
     *     try {
     *         block(resource)
     *     } finally {
     *         resourcePool.trySend(resource)
     *     }
     * }
     * ```
     */
    public fun tryReceive(): ChannelResult<E>

    /**
     * Returns a new iterator to receive elements from this channel using a `for` loop.
     * Iteration completes normally when the channel [is closed for `receive`][isClosedForReceive] without a cause and
     * throws the exception passed to [close][SendChannel.close] if there was one.
     *
     * Instances of [ChannelIterator] are not thread-safe and shall not be used from concurrent coroutines.
     *
     * Example:
     *
     * ```
     * val channel = produce<Int> {
     *     repeat(1000) {
     *         send(it)
     *     }
     * }
     * for (v in channel) {
     *     println(v)
     * }
     * ```
     *
     * Note that if an early return happens from the `for` loop, the channel does not get cancelled.
     * To forbid sending new elements after the iteration is completed, use [consumeEach] or
     * call [cancel] manually.
     */
    public operator fun iterator(): ChannelIterator<E>

    /**
     * [Closes][SendChannel.close] the channel for new elements and removes all existing ones.
     *
     * A [cause] can be used to specify an error message or to provide other details on
     * the cancellation reason for debugging purposes.
     * If the cause is not specified, then an instance of [CancellationException] with a
     * default message is created to [close][SendChannel.close] the channel.
     *
     * If the channel was already [closed][SendChannel.close],
     * [cancel] only has the effect of removing all elements from the channel.
     *
     * Immediately after the invocation of this function,
     * [isClosedForReceive] and, on the [SendChannel] side, [isClosedForSend][SendChannel.isClosedForSend]
     * start returning `true`.
     * Any attempt to send to or receive from this channel will lead to a [CancellationException].
     * This also applies to the existing senders and receivers that are suspended at the time of the call:
     * they will be resumed with a [CancellationException] immediately after [cancel] is called.
     *
     * If the channel has an `onUndeliveredElement` callback installed, this function will invoke it for each of the
     * elements still in the channel, since these elements will be inaccessible otherwise.
     * If the callback is not installed, these elements will simply be removed from the channel for garbage collection.
     *
     * ```
     * val channel = Channel<Int>()
     * channel.send(1)
     * channel.send(2)
     * channel.cancel()
     * channel.trySend(3) // returns ChannelResult.isClosed
     * for (element in channel) { println(element) } // prints nothing
     * ```
     *
     * [consume] and [consumeEach] are convenient shorthands for cancelling the channel after the single consumer
     * has finished processing.
     */
    public fun cancel(cause: CancellationException? = null)

    /**
     * @suppress This method implements old version of JVM ABI. Use [cancel].
     */
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    public fun cancel(): Unit = cancel(null)

    /**
     * @suppress This method has bad semantics when cause is not a [CancellationException]. Use [cancel].
     */
    @Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.2.0, binary compatibility with versions <= 1.1.x")
    public fun cancel(cause: Throwable? = null): Boolean

    /**
     * **Deprecated** poll method.
     *
     * This method was deprecated in the favour of [tryReceive].
     * It has proven itself as error-prone method in Channel API:
     *
     * - Nullable return type creates the false sense of security, implying that `null`
     *   is returned instead of throwing an exception.
     * - It was used mostly from non-suspending APIs where CancellationException triggered
     *   internal failures in the application (the most common source of bugs).
     * - Its name was not aligned with the rest of the API and tried to mimic Java's queue instead.
     *
     * See https://github.com/Kotlin/kotlinx.coroutines/issues/974 for more context.
     *
     * ### Replacement note
     *
     * The replacement `tryReceive().getOrNull()` is a default that ignores all close exceptions and
     * proceeds with `null`, while `poll` throws an exception if the channel was closed with an exception.
     * Replacement with the very same 'poll' semantics is `tryReceive().onClosed { if (it != null) throw it }.getOrNull()`
     *
     * @suppress **Deprecated**.
     */
    @Deprecated(
        level = DeprecationLevel.ERROR,
        message = "Deprecated in the favour of 'tryReceive'. " +
            "Please note that the provided replacement does not rethrow channel's close cause as 'poll' did, " +
            "for the precise replacement please refer to the 'poll' documentation",
        replaceWith = ReplaceWith("tryReceive().getOrNull()")
    ) // Warning since 1.5.0, error since 1.6.0, not hidden until 1.8+ because API is quite widespread
    public fun poll(): E? {
        val result = tryReceive()
        if (result.isSuccess) return result.getOrThrow()
        throw recoverStackTrace(result.exceptionOrNull() ?: return null)
    }

    /**
     * This function was deprecated since 1.3.0 and is no longer recommended to use
     * or to implement in subclasses.
     *
     * It had the following pitfalls:
     * - Didn't allow to distinguish 'null' as "closed channel" from "null as a value"
     * - Was throwing if the channel has failed even though its signature may suggest it returns 'null'
     * - It didn't really belong to core channel API and can be exposed as an extension instead.
     *
     * ### Replacement note
     *
     * The replacement `receiveCatching().getOrNull()` is a safe default that ignores all close exceptions and
     * proceeds with `null`, while `receiveOrNull` throws an exception if the channel was closed with an exception.
     * Replacement with the very same `receiveOrNull` semantics is `receiveCatching().onClosed { if (it != null) throw it }.getOrNull()`.
     *
     * @suppress **Deprecated**
     */
    @Suppress("INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")
    @LowPriorityInOverloadResolution
    @Deprecated(
        message = "Deprecated in favor of 'receiveCatching'. " +
            "Please note that the provided replacement does not rethrow channel's close cause as 'receiveOrNull' did, " +
            "for the detailed replacement please refer to the 'receiveOrNull' documentation",
        level = DeprecationLevel.ERROR,
        replaceWith = ReplaceWith("receiveCatching().getOrNull()")
    ) // Warning since 1.3.0, error in 1.5.0, cannot be hidden due to deprecated extensions
    public suspend fun receiveOrNull(): E? = receiveCatching().getOrNull()

    /**
     * This function was deprecated since 1.3.0 and is no longer recommended to use
     * or to implement in subclasses.
     * See [receiveOrNull] documentation.
     *
     * @suppress **Deprecated**: in favor of onReceiveCatching extension.
     */
    @Suppress("DEPRECATION_ERROR")
    @Deprecated(
        message = "Deprecated in favor of onReceiveCatching extension",
        level = DeprecationLevel.ERROR,
        replaceWith = ReplaceWith("onReceiveCatching")
    ) // Warning since 1.3.0, error in 1.5.0, will be hidden or removed in 1.7.0
    public val onReceiveOrNull: SelectClause1<E?> get() = (this as BufferedChannel<E>).onReceiveOrNull
}

/**
 * A discriminated union representing a channel operation result.
 * It encapsulates the knowledge of whether the operation succeeded, failed with an option to retry,
 * or failed because the channel was closed.
 *
 * If the operation was [successful][isSuccess], [T] is the result of the operation:
 * for example, for [ReceiveChannel.receiveCatching] and [ReceiveChannel.tryReceive],
 * it is the element received from the channel, and for [Channel.trySend], it is [Unit],
 * as the channel does not receive anything in return for sending a channel.
 * This value can be retrieved with [getOrNull] or [getOrThrow].
 *
 * If the operation [failed][isFailure], it does not necessarily mean that the channel itself is closed.
 * For example, [ReceiveChannel.receiveCatching] and [ReceiveChannel.tryReceive] can fail because the channel is empty,
 * and [Channel.trySend] can fail because the channel is full.
 *
 * If the operation [failed][isFailure] because the channel was closed for that operation, [isClosed] returns `true`.
 * The opposite is also true: if [isClosed] returns `true`, then the channel is closed for that operation
 * ([ReceiveChannel.isClosedForReceive] or [SendChannel.isClosedForSend]).
 * In this case, retrying the operation is meaningless: once closed, the channel will remain closed.
 * The [exceptionOrNull] function returns the reason the channel was closed, if any was given.
 *
 * Manually obtaining a [ChannelResult] instance is not supported.
 * See the documentation for [ChannelResult]-returning functions for usage examples.
 */
@JvmInline
public value class ChannelResult<out T>
@PublishedApi internal constructor(@PublishedApi internal val holder: Any?) {
    /**
     * Whether the operation succeeded.
     *
     * If this returns `true`, the operation was successful.
     * In this case, [getOrNull] and [getOrThrow] can be used to retrieve the value.
     *
     * If this returns `false`, the operation failed.
     * [isClosed] can be used to determine whether the operation failed because the channel was closed
     * (and therefore retrying the operation is meaningless).
     *
     * ```
     * val result = channel.tryReceive()
     * if (result.isSuccess) {
     *    println("Successfully received the value ${result.getOrThrow()}")
     * } else {
     *    println("Failed to receive the value.")
     *    if (result.isClosed) {
     *        println("The channel is closed.")
     *        if (result.exceptionOrNull() != null) {
     *            println("The reason: ${result.exceptionOrNull()}")
     *        }
     *    }
     * }
     * ```
     *
     * [isFailure] is a shorthand for `!isSuccess`.
     * [getOrNull] can simplify [isSuccess] followed by [getOrThrow] into just one check if [T] is known
     * to be non-nullable.
     */
    public val isSuccess: Boolean get() = holder !is Failed

    /**
     * Whether the operation failed.
     *
     * A shorthand for `!isSuccess`. See [isSuccess] for more details.
     */
    public val isFailure: Boolean get() = holder is Failed

    /**
     * Whether the operation failed because the channel was closed.
     *
     * If this returns `true`, the channel was closed for the operation that returned this result.
     * In this case, retrying the operation is meaningless: once closed, the channel will remain closed.
     * [isSuccess] will return `false`.
     * [exceptionOrNull] can be used to determine the reason the channel was [closed][SendChannel.close]
     * if one was given.
     *
     * If this returns `false`, subsequent attempts to perform the same operation may succeed.
     *
     * ```
     * val result = channel.trySend(42)
     * if (result.isClosed) {
     *     println("The channel is closed.")
     *     if (result.exceptionOrNull() != null) {
     *         println("The reason: ${result.exceptionOrNull()}")
     *     }
     * }
     */
    public val isClosed: Boolean get() = holder is Closed

    /**
     * Returns the encapsulated [T] if the operation succeeded, or `null` if it failed.
     *
     * For non-nullable [T], the following code can be used to handle the result:
     * ```
     * val result = channel.tryReceive()
     * val value = result.getOrNull()
     * if (value == null) {
     *     if (result.isClosed) {
     *         println("The channel is closed.")
     *         if (result.exceptionOrNull() != null) {
     *             println("The reason: ${result.exceptionOrNull()}")
     *         }
     *     }
     *     return
     * }
     * println("Successfully received the value $value")
     * ```
     *
     * If [T] is nullable, [getOrThrow] together with [isSuccess] is a more reliable way to handle the result.
     */
    @Suppress("UNCHECKED_CAST")
    public fun getOrNull(): T? = if (holder !is Failed) holder as T else null

    /**
     *  Returns the encapsulated [T] if the operation succeeded, or throws the encapsulated exception if it failed.
     *
     *  Example:
     *  ```
     *  val result = channel.tryReceive()
     *  if (result.isSuccess) {
     *      println("Successfully received the value ${result.getOrThrow()}")
     *  }
     *  ```
     *
     *  @throws IllegalStateException if the operation failed, but the channel was not closed with a cause.
     */
    public fun getOrThrow(): T {
        @Suppress("UNCHECKED_CAST")
        if (holder !is Failed) return holder as T
        if (holder is Closed) {
            check(holder.cause != null) { "Trying to call 'getOrThrow' on a channel closed without a cause" }
            throw holder.cause
        }
        error("Trying to call 'getOrThrow' on a failed result of a non-closed channel")
    }

    /**
     * Returns the exception with which the channel was closed, or `null` if the channel was not closed or was closed
     * without a cause.
     *
     * [exceptionOrNull] can only return a non-`null` value if [isClosed] is `true`,
     * but even if [isClosed] is `true`,
     * [exceptionOrNull] can still return `null` if the channel was closed without a cause.
     *
     * ```
     * val result = channel.tryReceive()
     * if (result.isClosed) {
     *     // Now we know not to retry the operation later.
     *     // Check if the channel was closed with a cause and rethrow the exception:
     *     result.exceptionOrNull()?.let { throw it }
     *     // Otherwise, the channel was closed without a cause.
     * }
     * ```
     */
    public fun exceptionOrNull(): Throwable? = (holder as? Closed)?.cause

    internal open class Failed {
        override fun toString(): String = "Failed"
    }

    internal class Closed(@JvmField val cause: Throwable?): Failed() {
        override fun equals(other: Any?): Boolean = other is Closed && cause == other.cause
        override fun hashCode(): Int = cause.hashCode()
        override fun toString(): String = "Closed($cause)"
    }

    /**
     * @suppress **This is internal API and it is subject to change.**
     */
    @InternalCoroutinesApi
    public companion object {
        private val failed = Failed()

        @InternalCoroutinesApi
        public fun <E> success(value: E): ChannelResult<E> =
            ChannelResult(value)

        @InternalCoroutinesApi
        public fun <E> failure(): ChannelResult<E> =
            ChannelResult(failed)

        @InternalCoroutinesApi
        public fun <E> closed(cause: Throwable?): ChannelResult<E> =
            ChannelResult(Closed(cause))
    }

    public override fun toString(): String =
        when (holder) {
            is Closed -> holder.toString()
            else -> "Value($holder)"
        }
}

/**
 * Returns the encapsulated value if the operation [succeeded][ChannelResult.isSuccess], or the
 * result of [onFailure] function for [ChannelResult.exceptionOrNull] otherwise.
 *
 * A shorthand for `if (isSuccess) getOrNull() else onFailure(exceptionOrNull())`.
 *
 * @see ChannelResult.getOrNull
 * @see ChannelResult.exceptionOrNull
 */
@OptIn(ExperimentalContracts::class)
public inline fun <T> ChannelResult<T>.getOrElse(onFailure: (exception: Throwable?) -> T): T {
    contract {
        callsInPlace(onFailure, InvocationKind.AT_MOST_ONCE)
    }
    @Suppress("UNCHECKED_CAST")
    return if (holder is ChannelResult.Failed) onFailure(exceptionOrNull()) else holder as T
}

/**
 * Performs the given [action] on the encapsulated value if the operation [succeeded][ChannelResult.isSuccess].
 * Returns the original `ChannelResult` unchanged.
 *
 * A shorthand for `this.also { if (isSuccess) action(getOrThrow()) }`.
 */
@OptIn(ExperimentalContracts::class)
public inline fun <T> ChannelResult<T>.onSuccess(action: (value: T) -> Unit): ChannelResult<T> {
    contract {
        callsInPlace(action, InvocationKind.AT_MOST_ONCE)
    }
    @Suppress("UNCHECKED_CAST")
    if (holder !is ChannelResult.Failed) action(holder as T)
    return this
}

/**
 * Performs the given [action] if the operation [failed][ChannelResult.isFailure].
 * The result of [ChannelResult.exceptionOrNull] is passed to the [action] parameter.
 *
 * Returns the original `ChannelResult` unchanged.
 *
 * A shorthand for `this.also { if (isFailure) action(exceptionOrNull()) }`.
 */
@OptIn(ExperimentalContracts::class)
public inline fun <T> ChannelResult<T>.onFailure(action: (exception: Throwable?) -> Unit): ChannelResult<T> {
    contract {
        callsInPlace(action, InvocationKind.AT_MOST_ONCE)
    }
    if (holder is ChannelResult.Failed) action(exceptionOrNull())
    return this
}

/**
 * Performs the given [action] if the operation failed because the channel was [closed][ChannelResult.isClosed] for
 * that operation.
 * The result of [ChannelResult.exceptionOrNull] is passed to the [action] parameter.
 *
 * It is guaranteed that if action is invoked, then the channel is either [closed for send][Channel.isClosedForSend]
 * or is [closed for receive][Channel.isClosedForReceive] depending on the failed operation.
 *
 * Returns the original `ChannelResult` unchanged.
 *
 * A shorthand for `this.also { if (isClosed) action(exceptionOrNull()) }`.
 */
@OptIn(ExperimentalContracts::class)
public inline fun <T> ChannelResult<T>.onClosed(action: (exception: Throwable?) -> Unit): ChannelResult<T> {
    contract {
        callsInPlace(action, InvocationKind.AT_MOST_ONCE)
    }
    if (holder is ChannelResult.Closed) action(exceptionOrNull())
    return this
}

/**
 * Iterator for a [ReceiveChannel].
 * Instances of this interface are *not thread-safe* and shall not be used from concurrent coroutines.
 */
public interface ChannelIterator<out E> {
    /**
     * Prepare an element for retrieval by the invocation of [next].
     *
     * - If the element that was retrieved by an earlier [hasNext] call was not yet consumed by [next], returns `true`.
     * - If the channel has an element available, returns `true` and removes it from the channel.
     *   This element will be returned by the subsequent invocation of [next].
     * - If the channel is [closed for receiving][ReceiveChannel.isClosedForReceive] without a cause, returns `false`.
     * - If the channel is closed with a cause, throws the original [close][SendChannel.close] cause exception.
     * - If the channel is not closed but does not contain an element,
     *   suspends until either an element is sent to the channel or the channel gets closed.
     *
     * This suspending function is cancellable: if the [Job] of the current coroutine is cancelled while this
     * suspending function is waiting, this function immediately resumes with [CancellationException].
     * There is a **prompt cancellation guarantee**: even if [hasNext] retrieves the element from the channel during
     * its operation, but was cancelled while suspended, [CancellationException] will be thrown.
     * See [suspendCancellableCoroutine] for low-level details.
     *
     * Because of the prompt cancellation guarantee, some values retrieved from the channel can become lost.
     * See the "Undelivered elements" section in the [Channel] documentation
     * for details on handling undelivered elements.
     *
     * Note that this function does not check for cancellation when it is not suspended, that is,
     * if the next element is immediately available.
     * Use [ensureActive] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     */
    public suspend operator fun hasNext(): Boolean

    @Deprecated(message = "Since 1.3.0, binary compatibility with versions <= 1.2.x", level = DeprecationLevel.HIDDEN)
    @Suppress("INAPPLICABLE_JVM_NAME")
    @JvmName("next")
    public suspend fun next0(): E {
        /*
         * Before 1.3.0 the "next()" could have been used without invoking "hasNext" first and there were code samples
         * demonstrating this behavior, so we preserve this logic for full binary backwards compatibility with previously
         * compiled code.
         */
        if (!hasNext()) throw ClosedReceiveChannelException(DEFAULT_CLOSE_MESSAGE)
        return next()
    }

    /**
     * Retrieves the element removed from the channel by the preceding call to [hasNext], or
     * throws an [IllegalStateException] if [hasNext] was not invoked.
     *
     * This method can only be used together with [hasNext]:
     * ```
     * while (iterator.hasNext()) {
     *     val element = iterator.next()
     *     // ... handle the element ...
     * }
     * ```
     *
     * A more idiomatic way to iterate over a channel is to use a `for` loop:
     * ```
     * for (element in channel) {
     *    // ... handle the element ...
     * }
     * ```
     *
     * This method never throws if [hasNext] returned `true`.
     * If [hasNext] threw the cause with which the channel was closed, this method will rethrow the same exception.
     * If [hasNext] returned `false` because the channel was closed without a cause, this method throws
     * a [ClosedReceiveChannelException].
     */
    public operator fun next(): E
}

/**
 * Channel is a non-blocking primitive for communication between a sender (via [SendChannel]) and a receiver (via [ReceiveChannel]).
 * Conceptually, a channel is similar to `java.util.concurrent.BlockingQueue`,
 * but it has suspending operations instead of blocking ones and can be [closed][SendChannel.close].
 *
 * ### Channel capacity
 *
 * Most ways to create a [Channel] (in particular, the `Channel()` factory function) allow specifying a capacity,
 * which determines how elements are buffered in the channel.
 * There are several predefined constants for the capacity that have special behavior:
 *
 * - [Channel.RENDEZVOUS] (or 0) creates a _rendezvous_ channel, which does not have a buffer at all.
 *   Instead, the sender and the receiver must rendezvous (meet):
 *   [SendChannel.send] suspends until another coroutine invokes [ReceiveChannel.receive], and vice versa.
 * - [Channel.CONFLATED] creates a buffer for a single element and automatically changes the
 *   [buffer overflow strategy][BufferOverflow] to [BufferOverflow.DROP_OLDEST].
 * - [Channel.UNLIMITED] creates a channel with an unlimited buffer, which never suspends the sender.
 * - [Channel.BUFFERED] creates a channel with a buffer whose size depends on
 *   the [buffer overflow strategy][BufferOverflow].
 *
 * See each constant's documentation for more details.
 *
 * If the capacity is positive but less than [Channel.UNLIMITED], the channel has a buffer with the specified capacity.
 * It is safe to construct a channel with a large buffer, as memory is only allocated gradually as elements are added.
 *
 * Constructing a channel with a negative capacity not equal to a predefined constant is not allowed
 * and throws an [IllegalArgumentException].
 *
 * ### Buffer overflow
 *
 * Some ways to create a [Channel] also expose a [BufferOverflow] parameter (by convention, `onBufferOverflow`),
 * which does not affect the receiver but determines the behavior of the sender when the buffer is full.
 * The options include [suspending][BufferOverflow.SUSPEND] until there is space in the buffer,
 * [dropping the oldest element][BufferOverflow.DROP_OLDEST] to make room for the new one, or
 * [dropping the element to be sent][BufferOverflow.DROP_LATEST]. See the [BufferOverflow] documentation.
 *
 * By convention, the default value for [BufferOverflow] whenever it can not be configured is [BufferOverflow.SUSPEND].
 *
 * See the [Channel.RENDEZVOUS], [Channel.CONFLATED], and [Channel.UNLIMITED] documentation for a description of how
 * they interact with the [BufferOverflow] parameter.
 *
 * ### Prompt cancellation guarantee
 *
 * All suspending functions with channels provide **prompt cancellation guarantee**.
 * If the job was cancelled while send or receive function was suspended, it will not resume successfully, even if it
 * already changed the channel's state, but throws a [CancellationException].
 * With a single-threaded [dispatcher][CoroutineDispatcher] like [Dispatchers.Main], this gives a
 * guarantee that the coroutine promptly reacts to the cancellation of its [Job] and does not resume its execution.
 *
 * > **Prompt cancellation guarantee** for channel operations was added in `kotlinx.coroutines` version `1.4.0`
 * > and has replaced the channel-specific atomic cancellation that was not consistent with other suspending functions.
 * > The low-level mechanics of prompt cancellation are explained in the [suspendCancellableCoroutine] documentation.
 *
 * ### Undelivered elements
 *
 * As a result of the prompt cancellation guarantee, when a closeable resource
 * (like an open file or a handle to another native resource) is transferred via a channel,
 * it can be successfully extracted from the channel,
 * but still be lost if the receiving operation is cancelled in parallel.
 *
 * The `Channel()` factory function has the optional parameter `onUndeliveredElement`.
 * When that parameter is set, the corresponding function is called once for each element
 * that was sent to the channel with the call to the [send][SendChannel.send] function but failed to be delivered,
 * which can happen in the following cases:
 *
 * - When an element is dropped due to the limited buffer capacity.
 *   This can happen when the overflow strategy is [BufferOverflow.DROP_LATEST] or [BufferOverflow.DROP_OLDEST].
 * - When the sending operations like [send][SendChannel.send] or [onSend][SendChannel.onSend]
 *   throw an exception because it was cancelled
 *   before it had a chance to actually send the element
 *   or because the channel was [closed][SendChannel.close] or [cancelled][ReceiveChannel.cancel].
 * - When the receiving operations like [receive][ReceiveChannel.receive],
 *   [onReceive][ReceiveChannel.onReceive], or [hasNext][ChannelIterator.hasNext]
 *   throw an exception after retrieving the element from the channel
 *   because of being cancelled before the code following them had a chance to resume.
 * - When the channel was [cancelled][ReceiveChannel.cancel], in which case `onUndeliveredElement` is called on every
 *   remaining element in the channel's buffer.
 *
 * Note that `onUndeliveredElement` is called synchronously in an arbitrary context.
 * It should be fast, non-blocking, and should not throw exceptions.
 * Any exception thrown by `onUndeliveredElement` is wrapped into an internal runtime exception
 * which is either rethrown from the caller method or handed off to the exception handler in the current context
 * (see [CoroutineExceptionHandler]) when one is available.
 *
 * A typical usage for `onUndeliveredElement` is to close a resource that is being transferred via the channel. The
 * following code pattern guarantees that opened resources are closed even if the producer, the consumer,
 * and/or the channel are cancelled. Resources are never lost.
 *
 * ```
 * // Create a channel with an onUndeliveredElement block that closes a resource
 * val channel = Channel<Resource>(onUndeliveredElement = { resource -> resource.close() })
 *
 * // Producer code
 * val resourceToSend = openResource()
 * channel.send(resourceToSend)
 *
 * // Consumer code
 * val resourceReceived = channel.receive()
 * try {
 *     // work with received resource
 * } finally {
 *     resourceReceived.close()
 * }
 * ```
 *
 * > Note that if any work happens between `openResource()` and `channel.send(...)`,
 * > it is your responsibility to ensure that resource gets closed in case this additional code fails.
 */
public interface Channel<E> : SendChannel<E>, ReceiveChannel<E> {
    /**
     * Constants for the channel factory function `Channel()`.
     */
    public companion object Factory {
        /**
         * An unlimited buffer capacity.
         *
         * `Channel(UNLIMITED)` creates a channel with an unlimited buffer, which never suspends the sender.
         * The total amount of elements that can be sent to the channel is limited only by the available memory.
         *
         * If [BufferOverflow] is specified for the channel, it is completely ignored,
         * as the channel never suspends the sender.
         *
         * ```
         * val channel = Channel<Int>(Channel.UNLIMITED)
         * repeat(1000) {
         *    channel.trySend(it)
         * }
         * repeat(1000) {
         *    check(channel.tryReceive().getOrNull() == it)
         * }
         * ```
         */
        public const val UNLIMITED: Int = Int.MAX_VALUE

        /**
         * The zero buffer capacity.
         *
         * For the default [BufferOverflow] value of [BufferOverflow.SUSPEND],
         * `Channel(RENDEZVOUS)` creates a channel without a buffer.
         * An element is transferred from the sender to the receiver only when [send] and [receive] invocations meet
         * in time (that is, they _rendezvous_),
         * so [send] suspends until another coroutine invokes [receive],
         * and [receive] suspends until another coroutine invokes [send].
         *
         * ```
         * val channel = Channel<Int>(Channel.RENDEZVOUS)
         * check(channel.trySend(5).isFailure) // sending fails: no receiver is waiting
         * launch(start = CoroutineStart.UNDISPATCHED) {
         *     val element = channel.receive() // suspends
         *     check(element == 3)
         * }
         * check(channel.trySend(3).isSuccess) // sending succeeds: receiver is waiting
         * ```
         *
         * If a different [BufferOverflow] is specified,
         * `Channel(RENDEZVOUS)` creates a channel with a buffer of size 1:
         *
         * ```
         * val channel = Channel<Int>(0, onBufferOverflow = BufferOverflow.DROP_OLDEST)
         * // None of the calls suspend, since the buffer overflow strategy is not SUSPEND
         * channel.send(1)
         * channel.send(2)
         * channel.send(3)
         * check(channel.receive() == 3)
         * ```
         */
        public const val RENDEZVOUS: Int = 0

        /**
         * A single-element buffer with conflating behavior.
         *
         * Specifying [CONFLATED] as the capacity in the `Channel(...)` factory function is equivalent to
         * creating a channel with a buffer of size 1 and a [BufferOverflow] strategy of [BufferOverflow.DROP_OLDEST]:
         * `Channel(1, onBufferOverflow = BufferOverflow.DROP_OLDEST)`.
         * Such a channel buffers at most one element and conflates all subsequent `send` and `trySend` invocations
         * so that the receiver always gets the last element sent, **losing** the previously sent elements:
         * see the "Undelivered elements" section in the [Channel] documentation.
         * [Sending][send] to this channel never suspends, and [trySend] always succeeds.
         *
         * ```
         * val channel = Channel<Int>(Channel.CONFLATED)
         * channel.send(1)
         * channel.send(2)
         * channel.send(3)
         * check(channel.receive() == 3)
         * ```
         *
         * Specifying a [BufferOverflow] other than [BufferOverflow.SUSPEND] is not allowed with [CONFLATED], and
         * an [IllegalArgumentException] is thrown if such a combination is used.
         * For creating a conflated channel that instead keeps the existing element in the channel and throws out
         * the new one, use `Channel(1, onBufferOverflow = BufferOverflow.DROP_LATEST)`.
         */
        public const val CONFLATED: Int = -1

        /**
         * A channel capacity marker that is substituted by the default buffer capacity.
         *
         * When passed as a parameter to the `Channel(...)` factory function, the default buffer capacity is used.
         * For [BufferOverflow.SUSPEND] (the default buffer overflow strategy), the default capacity is 64,
         * but on the JVM it can be overridden by setting the [DEFAULT_BUFFER_PROPERTY_NAME] system property.
         * The overridden value is used for all channels created with a default buffer capacity,
         * including those created in third-party libraries.
         *
         * ```
         * val channel = Channel<Int>(Channel.BUFFERED)
         * repeat(100) {
         *     channel.trySend(it)
         * }
         * channel.close()
         * // The check can fail if the default buffer capacity is changed
         * check(channel.toList() == (0..<64).toList())
         * ```
         *
         * If a different [BufferOverflow] is specified, `Channel(BUFFERED)` creates a channel with a buffer of size 1:
         *
         * ```
         * val channel = Channel<Int>(Channel.BUFFERED, onBufferOverflow = BufferOverflow.DROP_OLDEST)
         * channel.send(1)
         * channel.send(2)
         * channel.send(3)
         * channel.close()
         * check(channel.toList() == listOf(3))
         * ```
         */
        public const val BUFFERED: Int = -2

        // only for internal use, cannot be used with Channel(...)
        internal const val OPTIONAL_CHANNEL = -3

        /**
         * Name of the JVM system property for the default channel capacity (64 by default).
         *
         * See [BUFFERED] for details on how this property is used.
         *
         * Setting this property affects the default channel capacity for channel constructors,
         * channel-backed coroutines and flow operators that imply channel usage,
         * including ones defined in 3rd-party libraries.
         *
         * Usage of this property is highly discouraged and is intended to be used as a last-ditch effort
         * as an immediate measure for hot fixes and duct-taping.
         */
        @DelicateCoroutinesApi
        public const val DEFAULT_BUFFER_PROPERTY_NAME: String = "kotlinx.coroutines.channels.defaultBuffer"

        internal val CHANNEL_DEFAULT_CAPACITY = systemProp(DEFAULT_BUFFER_PROPERTY_NAME,
            64, 1, UNLIMITED - 1
        )
    }
}

/**
 * Creates a channel. See the [Channel] interface documentation for details.
 *
 * This function is the most flexible way to create a channel.
 * It allows specifying the channel's capacity, buffer overflow strategy, and an optional function to call
 * to handle undelivered elements.
 *
 * ```
 * val allocatedResources = HashSet<Int>()
 * // An autocloseable resource that must be closed when it is no longer needed
 * class Resource(val id: Int): AutoCloseable {
 *     init {
 *         allocatedResources.add(id)
 *     }
 *     override fun close() {
 *         allocatedResources.remove(id)
 *     }
 * }
 * // A channel with a 15-element buffer that drops the oldest element on buffer overflow
 * // and closes the elements that were not delivered to the consumer
 * val channel = Channel<Resource>(
 *     capacity = 15,
 *     onBufferOverflow = BufferOverflow.DROP_OLDEST,
 *     onUndeliveredElement = { element -> element.close() }
 * )
 * // A sender's view of the channel
 * val sendChannel: SendChannel<Resource> = channel
 * repeat(100) {
 *     sendChannel.send(Resource(it))
 * }
 * sendChannel.close()
 * // A receiver's view of the channel
 * val receiveChannel: ReceiveChannel<Resource> = channel
 * val receivedResources = receiveChannel.toList()
 * // Check that the last 15 sent resources were received
 * check(receivedResources.map { it.id } == (85 until 100).toList())
 * // Close the resources that were successfully received
 * receivedResources.forEach { it.close() }
 * // The dropped resources were closed by the channel itself
 * check(allocatedResources.isEmpty())
 * ```
 *
 * For a full explanation of every parameter and their interaction, see the [Channel] interface documentation.
 *
 * @param capacity either a positive channel capacity or one of the constants defined in [Channel.Factory].
 *   See the "Channel capacity" section in the [Channel] documentation.
 * @param onBufferOverflow configures an action on buffer overflow.
 *   See the "Buffer overflow" section in the [Channel] documentation.
 * @param onUndeliveredElement a function that is called when element was sent but was not delivered to the consumer.
 *   See the "Undelivered elements" section in the [Channel] documentation.
 * @throws IllegalArgumentException when [capacity] < -2
 */
public fun <E> Channel(
    capacity: Int = RENDEZVOUS,
    onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND,
    onUndeliveredElement: ((E) -> Unit)? = null
): Channel<E> =
    when (capacity) {
        RENDEZVOUS -> {
            if (onBufferOverflow == BufferOverflow.SUSPEND)
                BufferedChannel(RENDEZVOUS, onUndeliveredElement) // an efficient implementation of rendezvous channel
            else
                ConflatedBufferedChannel(1, onBufferOverflow, onUndeliveredElement) // support buffer overflow with buffered channel
        }
        CONFLATED -> {
            require(onBufferOverflow == BufferOverflow.SUSPEND) {
                "CONFLATED capacity cannot be used with non-default onBufferOverflow"
            }
            ConflatedBufferedChannel(1, BufferOverflow.DROP_OLDEST, onUndeliveredElement)
        }
        UNLIMITED -> BufferedChannel(UNLIMITED, onUndeliveredElement) // ignores onBufferOverflow: it has buffer, but it never overflows
        BUFFERED -> { // uses default capacity with SUSPEND
            if (onBufferOverflow == BufferOverflow.SUSPEND) BufferedChannel(CHANNEL_DEFAULT_CAPACITY, onUndeliveredElement)
            else ConflatedBufferedChannel(1, onBufferOverflow, onUndeliveredElement)
        }
        else -> {
            if (onBufferOverflow === BufferOverflow.SUSPEND) BufferedChannel(capacity, onUndeliveredElement)
            else ConflatedBufferedChannel(capacity, onBufferOverflow, onUndeliveredElement)
        }
    }

@Deprecated(level = DeprecationLevel.HIDDEN, message = "Since 1.4.0, binary compatibility with earlier versions")
public fun <E> Channel(capacity: Int = RENDEZVOUS): Channel<E> = Channel(capacity)

/**
 * Indicates an attempt to [send][SendChannel.send] to a [closed-for-sending][SendChannel.isClosedForSend] channel
 * that was [closed][SendChannel.close] without a cause.
 *
 * If a cause was provided, that cause is thrown from [send][SendChannel.send] instead of this exception.
 * In particular, if the channel was closed because it was [cancelled][ReceiveChannel.cancel],
 * this exception will never be thrown: either the `cause` of the cancellation is thrown,
 * or a new [CancellationException] gets constructed to be thrown from [SendChannel.send].
 *
 * This exception is a subclass of [IllegalStateException], because the sender should not attempt to send to a closed
 * channel after it itself has [closed][SendChannel.close] it, and indicates an error on the part of the programmer.
 * Usually, this exception can be avoided altogether by restructuring the code.
 */
public class ClosedSendChannelException(message: String?) : IllegalStateException(message)

/**
 * Indicates an attempt to [receive][ReceiveChannel.receive] from a
 * [closed-for-receiving][ReceiveChannel.isClosedForReceive] channel
 * that was [closed][SendChannel.close] without a cause.
 *
 * If a clause was provided, that clause is thrown from [receive][ReceiveChannel.receive] instead of this exception.
 * In particular, if the channel was closed because it was [cancelled][ReceiveChannel.cancel],
 * this exception will never be thrown: either the `cause` of the cancellation is thrown,
 * or a new [CancellationException] gets constructed to be thrown from [ReceiveChannel.receive].
 *
 * This exception is a subclass of [NoSuchElementException] to be consistent with plain collections.
 */
public class ClosedReceiveChannelException(message: String?) : NoSuchElementException(message)
