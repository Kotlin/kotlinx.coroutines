@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.flow.FlowCollector

/**
 * Used by IDEA debugger agent to support asynchronous stack traces in flows.
 * The agent requires a unique object present in both current and async stack traces,
 * so, without a wrapper, if two flows, `f1` and `f2`, emit equal values,
 * the agent could suggest `f1` as emitter for `f2.collect` and `f2` as emitter for `f1.collect`.
 */
internal class FlowValueWrapperInternal<T>(val value: T)

internal fun <T> wrapInternal(value: T): T = value
internal fun <T> unwrapInternal(value: T): T = value
internal fun <T> unwrapTyped(value: Any?): T = NULL.unbox(unwrapInternal(value))

// debugger agent transforms wrapInternal so it returns wrapInternalDebuggerCapture(value) instead of just value.
private fun wrapInternalDebuggerCapture(value: Any?): Any {
    if (value is FlowValueWrapperInternal<*>) {
        return value
    }
    return FlowValueWrapperInternal(value)
}

// debugger agent transforms unwrapInternal so it returns unwrapInternalDebuggerCapture(value) instead of just value
//
// normally, value is always FlowValueWrapperInternal, but potentially instrumentation may start
// in the middle of the execution (for example, when the debugger was attached to a running application),
// and the emitted value hadn't been wrapped
private fun unwrapInternalDebuggerCapture(value: Any?): Any? {
    val wrapper = value as? FlowValueWrapperInternal<*> ?: return value
    return wrapper.value
}

// Shouldn't be inlined, the method is instrumented by the IDEA debugger agent
internal suspend fun <T> FlowCollector<T>.emitInternal(value: Any?) {
    emit(unwrapTyped<T>(value))
}

// Shouldn't be inlined, the method is instrumented by the IDEA debugger agent
internal suspend fun <Unwrapped, R> debuggerCapture(value: Any?, block: suspend (Unwrapped) -> R): R {
    return block(unwrapInternal(value) as Unwrapped)
}
