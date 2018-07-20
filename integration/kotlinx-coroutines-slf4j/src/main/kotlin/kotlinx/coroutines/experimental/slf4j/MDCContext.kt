package kotlinx.coroutines.experimental.slf4j

import org.slf4j.MDC
import kotlin.coroutines.experimental.AbstractCoroutineContextElement
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.ContinuationInterceptor
import kotlin.coroutines.experimental.CoroutineContext

class MDCContext(
        private val context: CoroutineContext,
        private val contextMap: Map<String, String>? = MDC.getCopyOfContextMap()
) : AbstractCoroutineContextElement(ContinuationInterceptor), ContinuationInterceptor {

    override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> {
        val next = context[ContinuationInterceptor]

        val wrappedContinuation = Wrapper(continuation)

        return when (next) {
            null -> wrappedContinuation
            else -> next.interceptContinuation(wrappedContinuation)
        }
    }

    private inner class Wrapper<T>(private val continuation: Continuation<T>) : Continuation<T> {
        private inline fun wrap(block: () -> Unit) {
            try {
                contextMap?.let {
                    MDC.setContextMap(contextMap)
                }

                block()
            } finally {
                MDC.clear()
            }
        }

        override val context: CoroutineContext get() = continuation.context
        override fun resume(value: T) = wrap { continuation.resume(value) }
        override fun resumeWithException(exception: Throwable) = wrap { continuation.resumeWithException(exception) }
    }
}
