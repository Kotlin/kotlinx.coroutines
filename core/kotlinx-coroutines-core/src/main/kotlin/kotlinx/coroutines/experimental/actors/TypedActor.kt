package kotlinx.coroutines.experimental.actors

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import java.util.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

private typealias Act<T> = suspend TypedActor<T>.() -> Unit

open class TypedActor<T : TypedActor<T>>(
    context: CoroutineContext = DefaultDispatcher,
    parent: Job? = null,
    val start: CoroutineStart = CoroutineStart.LAZY,
    initialCapacity: Int = 16
) {
    private val actorContext: CoroutineContext
    private val sink: Any // TODO inline class Either<Workers|ReceiveChannel>
    private val job: Job

    init {
        val _dispatcherParent = dispatcherParent.get()
        val _dispatcher = dispatcher.get()

        // Fantastic builders and where to find them
        if (_dispatcherParent != null) {
            val parentJob = _dispatcherParent.job
            require(parent === null || parentJob === parent)
            actorContext = newCoroutineContext(context, parentJob)
            job = CompletableDeferred<Unit>(parentJob) // Empty job
            sink = CopyOnWriteArrayList<T>() // TODO hint about parallelism
        } else {
            sink = Channel<Act<T>>(initialCapacity)
            if (_dispatcher != null) {
                val parentJob = _dispatcher.job
                require(parent === null || parentJob === parent)
                actorContext = newCoroutineContext(context, parentJob)
                @Suppress("UNCHECKED_CAST", "LeakingThis")
                (_dispatcher.sink as MutableList<TypedActor<T>>).add(this)
            } else {
                actorContext = newCoroutineContext(context, parent)
            }
            job = launch(actorContext, start) { actorLoop() }
        }

        job.invokeOnCompletion { onClose() }
    }

    public fun close(): Boolean = job.cancel() // TODO channel.close() ?
    public suspend fun join(): Unit = job.join()

    /**
     * TODO document
     */
    protected suspend fun act(block: suspend T.() -> Unit) {
        job.start()
        val localSink = sink
        if (localSink is SendChannel<*>) {
            @Suppress("UNCHECKED_CAST")
            (localSink as SendChannel<suspend T.() -> Unit>).send(block)
        } else {
            require(localSink is List<*>)
            @Suppress("UNCHECKED_CAST")
            val list = localSink as List<T>
            // TODO round robin, pluggable policy?
            list[Random().nextInt(list.size)].act(block)
        }
    }

    protected open fun onClose() {}

    private suspend fun actorLoop() {
        if (sink !is ReceiveChannel<*>) return
        @Suppress("UNCHECKED_CAST")
        val channel = sink as ReceiveChannel<Act<T>>
        for (task in channel) {
            try {
                @Suppress("UNCHECKED_CAST")
                (this as T).task()
            } catch (e: Throwable) {
                handleCoroutineException(actorContext, e)
            }
        }
    }
}

private val dispatcherParent = ThreadLocal<TypedActor<*>?>()
private val dispatcher = ThreadLocal<TypedActor<*>>()

/**
 * Worker pool pattern support for typed actors.
 *
 * Creates [parallelism] actors by given [actorFactory] for parallel task processing
 * and wraps them in the actor of the same type, which dispatches all tasks from its mailbox to workers in round robin fashion.
 * Resulting hierarchy of actors will have the following form:
 * `parent (TypedActor<*>) <- router actor (T) <- parallelism * [worker actor (T)]`
 *
 * Close will be called on all created actors (TODO is this really that useful?).
 * It's guaranteed that [actorFactory] will be called exactly [parallelism] + 1 times.
 *
 * TODO provide example of usage
 * @param parallelism how many workers should be created for pool
 * @param parent owner of given worker (TODO allow orphan parallel workers?)
 * @param actorFactory factory to create actors for pool. Should be idempotent and all created actors should be indistinguishable
 */
fun <T : TypedActor<T>> concurrent(parallelism: Int, parent: TypedActor<*>, actorFactory: () -> T): T {
    require(parallelism > 1) { "Expected parallelism >1, but has $parallelism" }
    dispatcherParent.set(parent)
    val router: T
    try {
        router = actorFactory()
    } finally {
        dispatcherParent.set(null)
    }

    dispatcher.set(router)
    try {
        repeat(parallelism) {
            actorFactory()
        }
    } finally {
        dispatcher.set(null)
    }


    return router
}

fun <T : TypedActor<T>> concurrent(parallelism: Int, parent: Job, actorFactory: () -> T): T = TODO()
