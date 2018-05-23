package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.*

/**
 * [MonoActor] is the base for all stateful actors, who have to process one [type][T] of message
 * [MonoActor] has well-defined lifecycle described in [ActorTraits].
 * [MonoActor.receive] method is used to declare a message handler, which is parametrized by [T]
 * to provide better compile-type safety.
 *
 * Example:
 * ```
 * class ExampleActor : MonoActor<String>() {
 *
 *   override suspend fun receive(string: String) = act {
 *     println("Received $string")
 *   }
 * }
 *
 * // Sender
 * exampleActor.send("foo")
 * ```
 *
 * @param T type of the message this actor can handle
 */
abstract class MonoActor<T>(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16
) : AbstractActor<T>(context, parent, start, channelCapacity) {


    /**
     * Sends the message to the actor, which later will be processed by [receive]
     *
     * @throws ClosedSendChannelException if actor is [closed][close]
     */
    suspend fun send(message: T) {
        job.start()
        mailbox.send(message)
    }

    /**
     * Handler, which handles all sent messages
     *
     * @throws ClassCastException if actor was casted to raw type and [send] was invoked with wrong type of the argument
     */
    protected abstract suspend fun receive(message: T)

    override suspend fun actorLoop() {
        try {
            for (message in mailbox) {
                try {
                    receive(message)
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
