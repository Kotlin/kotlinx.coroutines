package kotlinx.coroutines.debug.internal

import kotlin.coroutines.jvm.internal.*

/**
 * A stack-trace represented as [CoroutineStackFrame].
 */
internal class StackTraceFrame(
    override val callerFrame: CoroutineStackFrame?,
    private val stackTraceElement: StackTraceElement
) : CoroutineStackFrame {
    override fun getStackTraceElement(): StackTraceElement = stackTraceElement
}
