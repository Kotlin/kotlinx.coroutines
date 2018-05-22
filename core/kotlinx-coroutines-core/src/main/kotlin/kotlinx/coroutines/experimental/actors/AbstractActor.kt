package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.*

/**
 * Base class for actors implementation, which provides implementation for [ActorTraits]
 *
 * @param T type of messages which are stored in the mailbox
 */
abstract class AbstractActor<T>(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16
) : ActorTraits() {

    internal val mailbox = Channel<T>(channelCapacity)
    protected val actorContext: CoroutineContext
    internal final override val job: Job

    init {
        val parentContext = newCoroutineContext(context, parent)
        job = launch(parentContext, start, parent) { actorLoop() }
        actorContext = job
        job.invokeOnCompletion { onClose() }
    }

    public override fun close() {
        mailbox.close()
    }

    /**
     * Kill the actor and its channel without letting the actor to process pending messages.
     * This is the last-ditch way to stop the actor which shouldn't be used normally.
     * [onClose] is called properly
     */
    public override fun kill() {
        job.cancel() // TODO throw actor killed exception?
    }

    internal abstract suspend fun actorLoop()
}
