package kotlinx.coroutines.experimental.actors

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlin.coroutines.experimental.*

/**
 * Base class for actors implementation, which provides implementation for [ActorTraits]
 * This class is not designed to be extended outside of kotlinx.coroutines, so it's internal
 *
 * @param T type of messages which are stored in the mailbox
 */
internal abstract class AbstractActor<T>(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    channelCapacity: Int = 16
) : ActorTraits() {

    internal val mailbox = Channel<T>(channelCapacity)
    public final override val job: Job = launch(context, start, parent) { actorLoop() }

    /*
     * Guard for onClose.
     * It's necessary to invoke onClose in the end of actor body even when we have job completion:
     * if actor decides to decompose its work, then onClose should be called *before* actor's body end,
     * otherwise delegated work will never be closed, because job completion will await all created children
     * to complete
     */
    private val onCloseInvoked = atomic(0)

    // Save an allocation
    private inner class OnCloseNode : JobNode<Job>(job) {
        override fun invoke(cause: Throwable?) {
            if (onCloseInvoked.compareAndSet(0, 1)) {
                onClose()
            }
        }
    }

    init {
        job.invokeOnCompletion(OnCloseNode())
    }

    public override fun close() {
        mailbox.close()
    }

    public override fun cancel() {
        job.cancel()
        mailbox.cancel()
    }

    private suspend fun actorLoop() {
        try {
            onStart()
            for (message in mailbox) {
                onMessage(message)
            }
        } catch (e: Throwable) {
            handleCoroutineException(coroutineContext, e)
        } finally {
            mailbox.close()
            if (onCloseInvoked.compareAndSet(0, 1)) {
                onClose()
            }
        }
    }

    internal abstract suspend fun onMessage(message: T)
}
