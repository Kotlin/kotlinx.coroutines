package kotlinx.coroutines.debug.internal

import kotlin.coroutines.jvm.internal.*

/**
 * A stack-trace represented as [CoroutineStackFrame].
 */
@PublishedApi
internal class StackTraceFrame internal constructor(
    override val callerFrame: CoroutineStackFrame?,
    // Used by the IDEA debugger via reflection and must be kept binary-compatible, see KTIJ-24102
    @JvmField public val stackTraceElement: StackTraceElement
) : CoroutineStackFrame {
    override fun getStackTraceElement(): StackTraceElement = stackTraceElement
}
