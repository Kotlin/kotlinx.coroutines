package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.intrinsics.startCoroutineUninterceptedOrReturn
import kotlin.coroutines.experimental.intrinsics.suspendCoroutineOrReturn

/**
 * Launches new coroutine without blocking current thread and returns a reference to the coroutine as a [Job].
 * The coroutine is cancelled when the resulting job is [cancelled][Job.cancel].
 *
 * The [context] for the new coroutine can be explicitly specified.
 * See [CoroutineDispatcher] for the standard context implementations that are provided by `kotlinx.coroutines`.
 * The [context][CoroutineScope.coroutineContext] of the parent coroutine from its [scope][CoroutineScope] may be used,
 * in which case the [Job] of the resulting coroutine is a child of the job of the parent coroutine.
 * The parent job may be also explicitly specified using [parent] parameter.
 *
 * If the context does not have any dispatcher nor any other [ContinuationInterceptor], then [DefaultDispatcher] is used.
 *
 * By default, the coroutine is immediately scheduled for execution.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 * An optional [start] parameter can be set to [CoroutineStart.LAZY] to start coroutine _lazily_. In this case,
 * the coroutine [Job] is created in _new_ state. It can be explicitly started with [start][Job.start] function
 * and will be started implicitly on the first invocation of [join][Job.join].
 *
 * Uncaught exceptions in this coroutine cancel parent job in the context by default
 * (unless [CoroutineExceptionHandler] is explicitly specified), which means that when `launch` is used with
 * the context of another coroutine, then any uncaught exception leads to the cancellation of parent coroutine.
 *
 * See [newCoroutineContext] for a description of debugging facilities that are available for newly created coroutine.
 *
 * @param context context of the coroutine. The default value is [DefaultDispatcher].
 * @param start coroutine start option. The default value is [CoroutineStart.DEFAULT].
 * @param parent explicitly specifies the parent job, overrides job from the [context] (if any).
 * @param block the coroutine code.
 */
public actual fun launch(
        context: CoroutineContext = DefaultDispatcher,
        start: CoroutineStart = CoroutineStart.DEFAULT,
        parent: Job? = null,
        block: suspend CoroutineScope.() -> Unit
): Job {
    val newContext = newCoroutineContext(context, parent)
    val coroutine = if (start.isLazy)
        LazyStandaloneCoroutine(newContext, block) else
        StandaloneCoroutine(newContext, active = true)
    coroutine.initParentJob(newContext[Job])
    start(block, coroutine, coroutine)
    return coroutine
}

/**
 * Calls the specified suspending block with a given coroutine context, suspends until it completes, and returns
 * the result.
 *
 * This function immediately applies dispatcher from the new context, shifting execution of the block into the
 * different thread inside the block, and back when it completes.
 * The specified [context] is added onto the current coroutine context for the execution of the block.
 *
 * An optional `start` parameter is used only if the specified `context` uses a different [CoroutineDispatcher] than
 * a current one, otherwise it is ignored.
 * By default, the coroutine is immediately scheduled for execution and can be cancelled
 * while it is waiting to be executed and it can be cancelled while the result is scheduled
 * to be processed by the invoker context.
 * Other options can be specified via `start` parameter. See [CoroutineStart] for details.
 * A value of [CoroutineStart.LAZY] is not supported and produces [IllegalArgumentException].
 */
public actual suspend fun <T> withContext(
    context: CoroutineContext,
    start: CoroutineStart = CoroutineStart.DEFAULT,
    block: suspend () -> T
): T = suspendCoroutineOrReturn sc@ { cont ->
    val oldContext = cont.context
    // fast path #1 if there is no change in the actual context:
    if (context === oldContext || context is CoroutineContext.Element && oldContext[context.key] === context)
        return@sc block.startCoroutineUninterceptedOrReturn(cont)
    // compute new context
    val newContext = oldContext + context
    // fast path #2 if the result is actually the same
    if (newContext === oldContext)
        return@sc block.startCoroutineUninterceptedOrReturn(cont)
    // fast path #3 if the new dispatcher is the same as the old one.
    // `equals` is used by design (see equals implementation is wrapper context like ExecutorCoroutineDispatcher)
    if (newContext[ContinuationInterceptor] == oldContext[ContinuationInterceptor]) {
        val newContinuation = RunContinuationDirect(newContext, cont)
        return@sc block.startCoroutineUninterceptedOrReturn(newContinuation)
    }
    // slowest path otherwise -- use new interceptor, sync to its result via a full-blown instance of RunCompletion
    require(!start.isLazy) { "$start start is not supported" }
    val completion = RunCompletion(
        context = newContext,
        delegate = cont,
        resumeMode = if (start == CoroutineStart.ATOMIC) MODE_ATOMIC_DEFAULT else MODE_CANCELLABLE)
    completion.initParentJob(newContext[Job]) // attach to job
    start(block, completion)
    completion.getResult()
}

/**
 * Runs new coroutine with the private event loop until its completion.
 * This function should not be used from coroutine. It is designed to bridge regular code
 * to libraries that are written in suspending style, to be used in `main` functions and in tests.
 *
 * The default [CoroutineDispatcher] for this builder in an implementation of [EventLoop] that processes continuations
 * in this blocked thread until the completion of this coroutine.
 * See [CoroutineDispatcher] for the other implementations that are provided by `kotlinx.coroutines`.
 *
 * @param context context of the coroutine. The default value is an implementation of [EventLoop].
 * @param block the coroutine code.
 */
public actual fun <T> runBlocking(context: CoroutineContext = EmptyCoroutineContext, block: suspend CoroutineScope.() -> T): T {
    val eventLoop = if (context[ContinuationInterceptor] == null) BlockingEventLoop() else null
    val newContext = newCoroutineContext(context + (eventLoop ?: EmptyCoroutineContext))
    val coroutine = BlockingCoroutine<T>(newContext, privateEventLoop = eventLoop != null)
    coroutine.initParentJob(newContext[Job])
    block.startCoroutine(coroutine, coroutine)
    return coroutine.joinBlocking()
}

// --------------- implementation ---------------

private open class StandaloneCoroutine(
        private val parentContext: CoroutineContext,
        active: Boolean
) : AbstractCoroutine<Unit>(parentContext, active) {
    override fun onCancellation(exceptionally: CompletedExceptionally?) {
        // note the use of the parent's job context below!
        if (exceptionally != null) handleCoroutineException(parentContext, exceptionally.exception)
    }
}

private class LazyStandaloneCoroutine(
        parentContext: CoroutineContext,
        private val block: suspend CoroutineScope.() -> Unit
) : StandaloneCoroutine(parentContext, active = false) {
    override fun onStart() {
        block.startCoroutineCancellable(this, this)
    }
}

private class RunContinuationDirect<in T>(
    override val context: CoroutineContext,
    continuation: Continuation<T>
) : Continuation<T> by continuation


@Suppress("UNCHECKED_CAST")
private class RunCompletion<in T>(
    override val context: CoroutineContext,
    delegate: Continuation<T>,
    resumeMode: Int
) : AbstractContinuation<T>(delegate, resumeMode) {
    override val hasCancellingState: Boolean
        get() = true
}

private class BlockingCoroutine<T>(
    parentContext: CoroutineContext,
    private val privateEventLoop: Boolean
) : AbstractCoroutine<T>(parentContext, true) {
    private val eventLoop: EventLoop? = parentContext[ContinuationInterceptor] as? EventLoop

    init {
        if (privateEventLoop) require(eventLoop is BlockingEventLoop)
    }

    fun joinBlocking(): T {
        while (true) {
            val delay = eventLoop?.processNextEvent() ?: Double.MAX_VALUE
            if (isCompleted) break
            if (delay > 0) {
                throw IllegalStateException("JS thread cannot be blocked, " +
                    "runBlocking { ... } cannot be waiting for its completion with timeout")
            }
        }
        // process queued events (that could have been added after last processNextEvent and before cancel
        if (privateEventLoop) (eventLoop as BlockingEventLoop).apply {
            // We exit the "while" loop above when this coroutine's state "isCompleted",
            // Here we should signal that BlockingEventLoop should not accept any more tasks
            isCompleted = true
            shutdown()
        }
        // now return result
        val state = this.state
        (state as? CompletedExceptionally)?.let { throw it.exception }
        @Suppress("UNCHECKED_CAST")
        return state as T
    }
}


