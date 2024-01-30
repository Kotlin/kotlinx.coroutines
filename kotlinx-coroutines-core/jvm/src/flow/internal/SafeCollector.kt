package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.coroutines.jvm.internal.*

@Suppress("UNCHECKED_CAST")
private val emitFun =
    FlowCollector<Any?>::emit as Function3<FlowCollector<Any?>, Any?, Continuation<Unit>, Any?>

/**
 * A safe collector is an instance of [FlowCollector] that ensures that neither context preservation
 * nor exception transparency invariants are broken. Instances of [SafeCollector] are used in flow
 * operators that provide raw access to the [FlowCollector] e.g. [Flow.transform].
 * Mechanically, each [emit] call captures [currentCoroutineContext], ensures it is not different from the
 * previously caught one and proceeds further. If an exception is thrown from the downstream,
 * it is caught, and any further attempts to [emit] lead to the [IllegalStateException].
 *
 * ### Performance hacks
 *
 * Implementor of [ContinuationImpl] (that will be preserved as ABI nearly forever)
 * in order to properly control `intercepted()` lifecycle.
 * The safe collector implements [ContinuationImpl] to pretend it *is* a state-machine of its own `emit` method.
 * It is [ContinuationImpl] and not any other [Continuation] subclass because only [ContinuationImpl] supports `intercepted()` caching.
 * This is the most performance-sensitive place in the overall flow pipeline, because otherwise safe collector is forced to allocate
 * a state machine on each element being emitted for each intermediate stage where the safe collector is present.
 *
 * See a comment to [emit] for the explanation of what and how is being optimized.
 */
@Suppress("CANNOT_OVERRIDE_INVISIBLE_MEMBER", "INVISIBLE_MEMBER", "INVISIBLE_REFERENCE", "UNCHECKED_CAST")
internal actual class SafeCollector<T> actual constructor(
    @JvmField internal actual val collector: FlowCollector<T>,
    @JvmField internal actual val collectContext: CoroutineContext
) : FlowCollector<T>, ContinuationImpl(NoOpContinuation, EmptyCoroutineContext), CoroutineStackFrame {

    override val callerFrame: CoroutineStackFrame? get() = completion_ as? CoroutineStackFrame

    override fun getStackTraceElement(): StackTraceElement? = null

    @JvmField // Note, it is non-capturing lambda, so no extra allocation during init of SafeCollector
    internal actual val collectContextSize = collectContext.fold(0) { count, _ -> count + 1 }

    // Either context of the last emission or wrapper 'DownstreamExceptionContext'
    private var lastEmissionContext: CoroutineContext? = null
    // Completion if we are currently suspended or within completion_ body or null otherwise
    private var completion_: Continuation<Unit>? = null

    /*
     * This property is accessed in two places:
     * - ContinuationImpl invokes this in its `releaseIntercepted` as `context[ContinuationInterceptor]!!`
     * - When we are within a callee, it is used to create its continuation object with this collector as completion_
     */
    override val context: CoroutineContext
        get() = lastEmissionContext ?: EmptyCoroutineContext

    override fun invokeSuspend(result: Result<Any?>): Any {
        result.onFailure { lastEmissionContext = DownstreamExceptionContext(it, context) }
        completion_?.resumeWith(result as Result<Unit>)
        return COROUTINE_SUSPENDED
    }

    // Escalate visibility to manually release intercepted continuation
    public actual override fun releaseIntercepted() {
        super.releaseIntercepted()
    }

    /**
     * This is a crafty implementation of state-machine reusing.
     *
     * First it checks that it is not used concurrently (which we explicitly prohibit), and
     * then just caches an instance of the completion_ in order to avoid extra allocation on each emit,
     * making it effectively garbage-free on its hot-path.
     *
     * See `emit` overload.
     */
    actual override suspend fun emit(value: T) {
        // NB: it is a tail-call, so we are sure `uCont` is the completion of the emit's **caller**.
        return suspendCoroutineUninterceptedOrReturn sc@{ uCont ->
            try {
                emit(uCont, value)
            } catch (e: Throwable) {
                // Save the fact that exception from emit (or even check context) has been thrown
                // Note, that this can the first emit and lastEmissionContext may not be saved yet,
                // hence we use `uCont.context` here.
                lastEmissionContext = DownstreamExceptionContext(e, uCont.context)
                throw e
            }
        }
    }

    /**
     * Here we use the following trick:
     * - Perform all the required checks
     * - Having a non-intercepted, non-cancellable caller's `uCont`, we leverage our implementation knowledge
     *   and invoke `collector.emit(T)` as `collector.emit(value: T, completion: Continuation), passing `this`
     *   as the completion. We also setup `this` state, so if the `completion.resume` is invoked, we are
     *   invoking `uCont.resume` properly in accordance with `ContinuationImpl`/`BaseContinuationImpl` internal invariants.
     *
     * Note that in such scenarios, `collector.emit` completion is the current instance of SafeCollector and thus is reused.
     */
    private fun emit(uCont: Continuation<Unit>, value: T): Any? {
        val currentContext = uCont.context
        currentContext.ensureActive()
        // This check is triggered once per flow on a happy path.
        val previousContext = lastEmissionContext
        if (previousContext !== currentContext) {
            checkContext(currentContext, previousContext, value)
            lastEmissionContext = currentContext
        }
        completion_ = uCont
        val result = emitFun(collector as FlowCollector<Any?>, value, this as Continuation<Unit>)
        /*
         * If the callee hasn't suspended, that means that it won't (it's forbidden) call 'resumeWith` (-> `invokeSuspend`)
         * and we don't have to retain a strong reference to it to avoid memory leaks.
         */
        if (result != COROUTINE_SUSPENDED) {
            completion_ = null
        }
        return result
    }

    private fun checkContext(
        currentContext: CoroutineContext,
        previousContext: CoroutineContext?,
        value: T
    ) {
        if (previousContext is DownstreamExceptionContext) {
            exceptionTransparencyViolated(previousContext, value)
        }
        checkContext(currentContext)
    }

    private fun exceptionTransparencyViolated(exception: DownstreamExceptionContext, value: Any?) {
        /*
         * Exception transparency ensures that if a `collect` block or any intermediate operator
         * throws an exception, then no more values will be received by it.
         * For example, the following code:
         * ```
         * val flow = flow {
         *     emit(1)
         *     try {
         *          emit(2)
         *     } catch (e: Exception) {
         *          emit(3)
         *     }
         * }
         * // Collector
         * flow.collect { value ->
         *     if (value == 2) {
         *         throw CancellationException("No more elements required, received enough")
         *     } else {
         *         println("Collected $value")
         *     }
         * }
         * ```
         * is expected to print "Collected 1" and then "No more elements required, received enough" exception,
         * but if exception transparency wasn't enforced, "Collected 1" and "Collected 3" would be printed instead.
         */
        error("""
            Flow exception transparency is violated:
                Previous 'emit' call has thrown exception ${exception.e}, but then emission attempt of value '$value' has been detected.
                Emissions from 'catch' blocks are prohibited in order to avoid unspecified behaviour, 'Flow.catch' operator can be used instead.
                For a more detailed explanation, please refer to Flow documentation.
            """.trimIndent())
    }
}

internal class DownstreamExceptionContext(
    @JvmField val e: Throwable,
    originalContext: CoroutineContext
) : CoroutineContext by originalContext

private object NoOpContinuation : Continuation<Any?> {
    override val context: CoroutineContext = EmptyCoroutineContext

    override fun resumeWith(result: Result<Any?>) {
        // Nothing
    }
}
