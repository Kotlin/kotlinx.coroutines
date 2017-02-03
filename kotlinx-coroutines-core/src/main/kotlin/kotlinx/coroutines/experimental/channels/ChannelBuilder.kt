package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

/**
 * Scope for [buildChannel].
 */
public interface ChannelBuilder<in E> : CoroutineScope, SendChannel<E>

/**
 * Return type for [buildChannel].
 */
public interface ChannelJob<out E> : Job, ReceiveChannel<E>

/**
 * Launches new coroutine without blocking current thread to send data over channel
 * and returns a reference to the coroutine as a [ChannelJob], which implements
 * both [Job] and [ReceiveChannel].
 * The scope of the coroutine contains [ChannelBuilder] interface, which implements
 * both [CoroutineScope] and [SendChannel], so that coroutine can invoke
 * [send][SendChannel.send] directly. The channel is [closed][SendChannel.close]
 * when the coroutine completes.
 * The running coroutine is cancelled when the its job is [cancelled][Job.cancel].
 *
 * The [context] for the new coroutine must be explicitly specified.
 * See [CoroutineDispatcher] for the standard [context] implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.context] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 *
 * Uncaught exceptions in this coroutine close the channel with this exception as a cause and
 * the resulting channel becomes _failed_, so that any attempt to receive from such a channel throws exception.
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 */
public fun <E> buildChannel(
    context: CoroutineContext,
    capacity: Int = 0,
    block: suspend ChannelBuilder<E>.() -> Unit
): ChannelJob<E> {
    val channel = Channel<E>(capacity)
    return ChannelCoroutine(newCoroutineContext(context), channel).apply {
        initParentJob(context[Job])
        block.startCoroutine(this, this)
    }
}

private class ChannelCoroutine<E>(
    context: CoroutineContext,
    val channel: Channel<E>
) : AbstractCoroutine<Unit>(context), ChannelBuilder<E>, ChannelJob<E>, Channel<E> by channel {
    override fun afterCompletion(state: Any?) {
        val cause = (state as? CompletedExceptionally)?.exception
        if (!channel.close(cause) && cause != null)
            handleCoroutineException(context, cause)
    }
}
