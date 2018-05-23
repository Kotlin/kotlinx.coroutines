package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.*

/**
 * [Actor] is the base for all stateful actors, who have to process more than one type of messages.
 * [Actor] has well-defined lifecycle described in [ActorTraits].
 *
 * To declare message handler, actor should have methods declared using [act],
 * which are used to send message "Send message which handler invokes `act` body"
 *
 * Example, where the actor asynchronously processes two types of messages:
 * ```
 * class ExampleActor : Actor() {
 *
 *   suspend fun sendInt(number: Int) = act {
 *     println("Received $number")
 *   }
 *
 *   suspend fun sendString(string: String) = act {
 *     println("Received $string")
 *   }
 * }
 *
 *
 * // Sender
 * exampleActor.sendInt(42)
 * ```
 */
abstract class Actor(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16
) : AbstractActor<suspend () -> Unit>(context, parent, start, channelCapacity) {

    /**
     * Schedules actor's [block] as a message to the actor mailbox.
     * All messages sent via [act] will be processed sequentially in the actor context.
     * Act semantics is equivalent to sending lambda to channel with receiver, which invokes
     * all sent lambdas
     *
     * @throws ClosedSendChannelException if actor is [closed][close]
     */
    protected suspend fun act(block: suspend () -> Unit) {
        job.start()
        mailbox.send(block)
    }

    internal override suspend fun actorLoop() {
        try {
            for (action in mailbox) {
                try {
                    action()
                } catch (e: Throwable) {
                    handleCoroutineException(actorContext, e)
                }
            }
        } finally {
            // Mailbox was closed, so it's time to cancel itself to properly kill all children and invoke cancellation handler
            job.cancel()
        }
    }
}
