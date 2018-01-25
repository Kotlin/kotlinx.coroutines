@file:JvmName("EventsHandler")

package kotlinx.coroutines.debug.manager

import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED
import kotlin.coroutines.experimental.jvm.internal.CoroutineImpl

var exceptions: AppendOnlyThreadSafeList<Throwable>? = null

// used from instrumented code
fun handleAfterSuspendCall(result: Any, continuation: Continuation<Any?>, functionCallKey: String) {
    if (result !== COROUTINE_SUSPENDED) return
    handleSuspendedCall(continuation, functionCallKey)
}

inline fun handle(message: () -> String, body: () -> Unit) {
    try {
        body()
    } catch (e: Throwable) {
        exceptions?.appendWithIndex(e)
        error { message() + " exception: ${e.stackTraceToString()}" }
    }
}

private fun handleSuspendedCall(continuation: Continuation<Any?>, functionCallKey: String) {
    require(allSuspendCallsMap.isNotEmpty(),
            { "allSuspendCallsMap is empty. Did you forget to build or read debugger indexes?" })
    val call = allSuspendCallsMap[functionCallKey]!!
    handle({ "handleAfterSuspendCall(${continuation.toStringSafe()}, $call)" }) {
        StacksManager.handleAfterSuspendFunctionReturn(continuation, call)
    }
}

// used from instrumented code
fun handleDoResumeEnter(completion: Continuation<Any?>, continuation: Continuation<Any?>, doResumeKey: String) {
    require(knownDoResumeFunctionsMap.isNotEmpty(),
            { "knownDoResumeFunctionsMap is empty. Did you forget to build or read debugger indexes?" })
    val func = knownDoResumeFunctionsMap[doResumeKey]!!
    handle({ "handleDoResumeEnter(${completion.toStringSafe()}, ${continuation.toStringSafe()}, $func)" }) {
        StacksManager.handleDoResumeEnter(completion, continuation, func)
    }
}

// used from instrumented code
fun maybeWrapCompletionAndCreateNewCoroutine(completion: Continuation<Any?>): Continuation<*> {
    handle({ "maybeWrapCompletionAndCreateNewCoroutine(${completion.toStringSafe()})" }) {
        if (completion is CoroutineImpl) {
            handleExistingCoroutine(completion)
            return completion
        }
        val wrapped = WrappedCompletion(completion)
        StacksManager.handleNewCoroutineCreated(wrapped)
        return wrapped
    }
    return completion // if crashed just return original
}

private fun handleExistingCoroutine(completion: CoroutineImpl) {
    val completionField = CoroutineImpl::class.java.getDeclaredField("completion")
    completionField.isAccessible = true
    debug {
        "existing coroutine with completion: " +
                "${(completionField[completion] as Continuation<*>).prettyHash}, " +
                "value: ${completion.prettyHash}, context: ${completion.context}"
    }
    StacksManager.ignoreNextDoResume(completion)
}
