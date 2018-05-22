package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*

/**
 * Actor traits, common for [Actor], [MonoActor] and [WorkerPoolActor]
 */
abstract class ActorTraits {

    internal abstract val job: Job

    /**
     * Closed the actor and its channel.
     * Before closing, the actor processes all pending messages and
     * then cancels its job (and all its children) and calls [onClose] when job and its children are cancelled
     */
    public abstract fun close()

    /**
     * Kill the actor and its channel without letting the actor to process pending messages.
     * This is the last-ditch way to stop the actor which shouldn't be used normally.
     * It's guaranteed that [onClose] will be called.
     */
    public abstract fun kill()

    /**
     * Handler which is invoked when he actor is closed or killed.
     * It's guaranteed that on the moment of invocation no more messages will be processed by the actor.
     */
    protected open fun onClose() {}

    /**
     * Waits until the actor is closed
     */
    public suspend fun join(): Unit = job.join()
}
