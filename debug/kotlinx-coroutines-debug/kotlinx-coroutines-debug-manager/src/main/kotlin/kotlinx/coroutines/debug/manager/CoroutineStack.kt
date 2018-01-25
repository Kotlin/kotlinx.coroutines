package kotlinx.coroutines.debug.manager

import java.lang.ref.WeakReference
import java.util.concurrent.atomic.AtomicInteger
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.CoroutineContext

private sealed class FrameId(value: Continuation<Any?>) : WeakId<Continuation<Any?>>(value)

val Any.prettyHash: String
    get() = System.identityHashCode(this).toString(16)

private class ContinuationId(value: Continuation<Any?>) : FrameId(value)
private class CompletionId(value: Continuation<Any?>) : FrameId(value)

private data class CoroutineStackFrame(val id: FrameId, val call: MethodCall) {
    override fun toString() = "$id, $call"
}

class WrappedContext(
        val name: String,
        context: CoroutineContext
) : WeakReference<CoroutineContext>(context) {
    val additionalInfo by lazy { get()?.toString() ?: "collected" }
    override fun toString() = name
    override fun equals(other: Any?) = other === this || other is WrappedContext && name == other.name
    override fun hashCode() = name.hashCode()
}

private val nextGeneratedId = AtomicInteger(0)

private fun CoroutineContext.wrap(): WrappedContext {
    // todo: rework this code when it becomes part of kotlinx.coroutines
    val parts = toString().drop(1).dropLast(1).split(", ").map {
        val firstParenthesis = it.indexOf('(')
        if (firstParenthesis == -1) it to ""
        else it.take(firstParenthesis) to it.drop(firstParenthesis + 1).dropLast(1)
    }.toMap()
    val name = parts["CoroutineName"] ?: "coroutine"
    val id = parts["CoroutineId"]
    val idStr = if (id != null) "#$id" else "$${nextGeneratedId.getAndIncrement()}"
    return WrappedContext("$name$idStr", this)
}

enum class CoroutineStatus { Created, Running, Suspended }

class CoroutineStack(val initialCompletion: WeakWrappedCompletion) {
    val context: WrappedContext = initialCompletion.value!!.context.wrap()
    val name: String = context.name
    var thread: Thread = Thread.currentThread() // latest known thread
        private set
    var status: CoroutineStatus = CoroutineStatus.Created
        private set
    var topFrameCompletion: WeakContinuation = initialCompletion //key to find stack for doResume
        private set
    private var topContinuation: WeakContinuation = initialCompletion
    private val stack = mutableListOf<CoroutineStackFrame>()
    private val unAppliedStack = mutableListOf<CoroutineStackFrame>()

    fun getSnapshot() = CoroutineSnapshot(name, context, status, thread, stack.map { it.call })

    /**
     * @return true if new frames were add to stack (it was suspended), false otherwise
     */
    fun handleSuspendFunctionReturn(completion: Continuation<Any?>, call: SuspendCall): Boolean {
        unAppliedStack.add(CoroutineStackFrame(CompletionId(completion), call))
        // todo: figure out how to minimize magic here and make it more robust
        if (completion === topContinuation.value && (call.fromMethod == stack.first().call.method
                || call.fromMethod.name == "doResume" && stack.first().call.method.name == "invoke")) {
            applyStack()
            return true
        }
        return false
    }

    private fun applyStack() {
        debug {
            buildString {
                append("stack applied\n")
                append("topCurrentContinuation hash: ${topContinuation.prettyHash}\n")
                append("initialCompletion: ${initialCompletion.prettyHash}\n")
                append("temp:\n${unAppliedStack.joinToString("\n")}\n")
                append("stack:\n${stack.joinToString("\n")}")
            }
        }
        status = CoroutineStatus.Suspended
        stack.addAll(0, unAppliedStack)
        topFrameCompletion = stack.first().id
        unAppliedStack.clear()
    }

    fun handleDoResume(
            completion: Continuation<Any?>,
            continuation: Continuation<Any?>,
            function: MethodId
    ): WeakContinuation {
        thread = Thread.currentThread()
        status = CoroutineStatus.Running
        if (stack.isEmpty()) {
            require(initialCompletion.value === completion)
            val continuationId = ContinuationId(continuation)
            topContinuation = continuationId
            stack.add(0, CoroutineStackFrame(continuationId,
                    DoResumeCall(function, MethodId.UNKNOWN, CallPosition.UNKNOWN)))
            return topContinuation
        }
        topContinuation = ContinuationId(continuation)
        topFrameCompletion = CompletionId(completion)
        val framesToRemove =
                stack.indexOfLast { it.id is CompletionId && it.id.value === continuation } + 1
        debug { "framesToRemove: $framesToRemove" }
        stack.dropInplace(framesToRemove)
        debug { "result stack size: ${stack.size}" }
        return topFrameCompletion
    }
}

/**
 * Remove first [n] elements inplace
 */
private fun MutableList<*>.dropInplace(n: Int) {
    val resultSize = size - n
    if (resultSize <= 0) clear()
    else
        while (size > resultSize)
            removeAt(0)
}