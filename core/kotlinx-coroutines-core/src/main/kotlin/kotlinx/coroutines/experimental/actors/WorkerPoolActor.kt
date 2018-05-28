package kotlinx.coroutines.experimental.actors

import kotlinx.atomicfu.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import java.util.*
import kotlin.coroutines.experimental.*

/**
 * TODO explain
 * 1) Worker pool concept
 * 2) Why this approach
 * 3) Job relationship
 */
abstract class WorkerPoolActor<T : WorkerPoolActor<T>>(
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.LAZY,
    workerChannelCapacity: Int = 16
) : ActorTraits() {

    protected val actorContext: CoroutineContext
    internal final override val job: Job

    private val mailboxOrDispatcher: Any
    @Suppress("UNCHECKED_CAST")
    private val mailbox: Channel<suspend T.() -> Unit>
        get() = mailboxOrDispatcher as Channel<suspend T.() -> Unit>

    @Suppress("UNCHECKED_CAST")
    private val workerPool: MutableList<T>
        get() = mailboxOrDispatcher as MutableList<T>

    private val activeWorkers = atomic(0)

    init {
        /*
         * Thread-locals for control flow.
         * If DISPATCHER_PARENT is set, then current worker is going to be
         * dispatcher actor (one user sees and uses).
         * Otherwise, it's worker pool actor, then DISPATCHER_ACTOR should
         * be present to register created worker
         */
        val parent = DISPATCHER_PARENT.get()
        if (parent != null) {
            // Init as dispatcher
            job = Job((parent as? WorkerPoolActor<*>)?.job ?: parent as? Job)
            job.start()
            actorContext = job
            job.invokeOnCompletion { onClose() } // Invoke onClose only once
            mailboxOrDispatcher = ArrayList<WorkerPoolActor<*>>()
        } else {
            // Init as worker
            @Suppress("UNCHECKED_CAST")
            val dispatcher = DISPATCHER_ACTOR.get() as? WorkerPoolActor<T>
                    ?: error("Parallel actor instantiation is allowed only from workerPool {} call")
            mailboxOrDispatcher = Channel<T>(workerChannelCapacity)
            val parentContext = newCoroutineContext(context, dispatcher.job)
            job = launch(parentContext, start) { workerActorLoop() }
            activeWorkers.incrementAndGet()
            job.invokeOnCompletion {
                if (activeWorkers.decrementAndGet() == 0) {
                    dispatcher.job.cancel()
                }
            }

            actorContext = job
            @Suppress("UNCHECKED_CAST", "LeakingThis")
            (dispatcher.workerPool).add(this as T)
        }
    }

    /**
     * TODO document
     */
    protected suspend fun act(block: suspend T.() -> Unit) {
        val pool = workerPool
        val target = pool[Random().nextInt(pool.size)]
        target.job.start()
        target.mailbox.send(block)
    }

    /**
     * Closed the worker pool.
     * Before closing, every pool worker processes all pending messages and then cancels its job (and all its children).
     * [onClose] is called once all workers are closed and their jobs are cancelled.
     */
    public override fun close() {
        workerPool.forEach { it.mailbox.close() }
    }

    /**
     * Kill the worker pool without letting workers to process pending messages.
     * This is the last-ditch way to stop the actor which shouldn't be used normally.
     * It's guaranteed that [onClose] will be called.
     */
    public override fun kill() {
        workerPool.forEach {
            it.job.cancel()
        }

        job.cancel()
    }

    private suspend fun workerActorLoop() {
        try {
            for (action in mailbox) {
                try {
                    @Suppress("UNCHECKED_CAST")
                    (this as T).action()
                } catch (e: Throwable) {
                    handleCoroutineException(actorContext, e)
                }
            }
        } finally {
            job.cancel()
        }
    }
}

// Thread locals to properly initialize worker pool actors.
// We can't use constructor arguments for that to provide
// flexible easy to use worker pool builders
private val DISPATCHER_PARENT = ThreadLocal<Any>()
private val NO_PARENT_MARKER = Any()
private val DISPATCHER_ACTOR = ThreadLocal<WorkerPoolActor<*>?>()

/**
 * Worker pool pattern support for typed actors.
 *
 * Creates [parallelism] actors by given [actorFactory] for parallel task processing
 * and wraps them in the actor of the same type, which dispatches all tasks from its mailbox to workers in round robin fashion.
 * Resulting hierarchy of actors will have the following form:
 * `parent (TypedActor<*>) <- router actor (T) <- parallelism * [worker actor (T)]`
 *
 * It's guaranteed that [actorFactory] will be called exactly [parallelism] + 1 times.
 *
 * @param parallelism how many workers should be created for pool
 * @param parent owner of given worker
 * @param actorFactory factory to create actors for pool. Should be idempotent and all created actors should be indistinguishable
 */
public fun <T : WorkerPoolActor<T>> workerPool(
    parallelism: Int,
    parent: ActorTraits? = null,
    actorFactory: () -> T
): T {
    return createWorkerPool(parallelism, parent, actorFactory)
}

public fun <T : WorkerPoolActor<T>> workerPool(parallelism: Int, parent: Job?, actorFactory: () -> T): T {
    return createWorkerPool(parallelism, parent, actorFactory)
}

private fun <T : WorkerPoolActor<T>> createWorkerPool(
    parallelism: Int,
    parent: Any?,
    actorFactory: () -> T
): T {
    require(parallelism > 0) { "Expected positive parallelism, but has $parallelism" }
    DISPATCHER_PARENT.set(parent ?: NO_PARENT_MARKER)
    val dispatcher = createDispatcherActor(actorFactory)
    createWorkers(dispatcher, parallelism, actorFactory)
    checkInvariant(dispatcher)
    return dispatcher
}

private fun checkInvariant(dispatcher: WorkerPoolActor<*>) {
    @Suppress("SENSELESS_COMPARISON")
    if (dispatcher.job == null) {
        throw IllegalStateException("""
            Dispatcher job isn't properly initialized,
            it usually indicates that actor constructor wasn't invoked.
            If you are using Mockito, use spy() instead of mock() to guarantee constructor
            invocation during worker pool construction.
        """.trimIndent())
    }
}

/**
 * TODO
 */
public fun <T> workerPoolActor(
    parallelism: Int,
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    start: CoroutineStart = CoroutineStart.LAZY,
    workerChannelCapacity: Int = 16,
    onMessage: suspend ActorTraits.(T) -> Unit
): Worker<T> {
    return workerPool(parallelism, parent) {
        Worker(
            onMessage,
            context,
            start,
            workerChannelCapacity = workerChannelCapacity)
    }
}

public class Worker<T>(
    private val onMessage: suspend ActorTraits.(T) -> Unit,
    context: CoroutineContext = DefaultDispatcher,
    start: CoroutineStart = CoroutineStart.LAZY,
    workerChannelCapacity: Int = 16
) : WorkerPoolActor<Worker<T>>(context, start, workerChannelCapacity) {

    suspend fun send(message: T) = act {
        onMessage(message)
    }
}

private fun <T : WorkerPoolActor<T>> createDispatcherActor(actorFactory: () -> T): T {
    val dispatcher: T
    try {
        dispatcher = actorFactory()
    } finally {
        DISPATCHER_PARENT.set(null)
    }
    return dispatcher
}

private fun <T : WorkerPoolActor<T>> createWorkers(dispatcher: T, parallelism: Int, actorFactory: () -> T) {
    DISPATCHER_ACTOR.set(dispatcher)
    try {
        repeat(parallelism) {
            actorFactory()
        }
    } finally {
        DISPATCHER_ACTOR.set(null)
    }
}
