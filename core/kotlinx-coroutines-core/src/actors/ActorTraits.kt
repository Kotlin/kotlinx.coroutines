package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.*

/**
 * Actor traits, common for [Actor] and [TypedActor].
 * Actor is a high-level abstraction for [channel][ReceiveChannel] and coroutine, which
 * sequentially processes messages from this channel.
 *
 * Actors are inspired by the Actor Model: <a href="http://en.wikipedia.org/wiki/Actor_model">http://en.wikipedia.org/wiki/Actor_model</a>,
 * but have slightly different semantics to expose type-safety over address transparency.
 *
 * Every actor has a [Job] associated with it, which lifecycle is tightly bound with actor lifecycle.
 *
 * Any actor has well-defined lifecycle:
 * -- Not started. Note that by default actors are started [lazily][CoroutineStart.LAZY]
 * -- Active. Actor is running and processing incoming messages
 * -- Closing. Actor's channel is closed for new messages, but actor is processing all pending messages,
 *    then invokes [onClose]. Can be triggered by [close] call
 * -- Closed. Actor and all its children (both actors and launched jobs) are completed, [job] is completed.
 * -- Cancelled. Actor's channel is closed for new messages, its job is cancelled, pending messages are not processed and
 *               hang in the channel, [onClose] is invoked. Can be triggered by [cancel] call
 *
 * Note:
 * [ActorTraits] doesn't have any variations of `send` method, because different implementations
 * have different ways to expose mailbox to provide static typing.
 */
abstract class ActorTraits {

    /**
     * Job identifying current actor and available from its [coroutineContext]
     *
     * Lifecycle:
     * If job is cancelled, actor is effectively killed
     * If actor is closed, job is completed as soon as all messages are processed and all launched children are completed
     * If actor is cancelled, job is cancelled immediately
     */
    public abstract val job: Job

    /**
     * Close the actor and its channel.
     * Before closing, the actor processes all pending messages and calls [onClose]
     */
    public abstract fun close()

    /**
     * Cancel the actor and its channel without letting the actor to process pending messages.
     * This is a last ditch way to stop the actor which shouldn't be used normally.
     * It's guaranteed that [onClose] will be called.
     */
    public abstract fun cancel()

    /**
     * Handler which is invoked when actor is started
     */
    protected open fun onStart() {}

    /**
     * Handler which is invoked when actor is closed or killed.
     * It's guaranteed that on the moment of invocation no more messages will be processed by the actor
     * and no more messages can be sent.
     * This handler is invoked even if actor wasn't started to properly cleanup resources owned by actor
     */
    protected open fun onClose() {}

    /**
     * Waits until the actor is completed or cancelled
     */
    public suspend fun join(): Unit = job.join()
}
