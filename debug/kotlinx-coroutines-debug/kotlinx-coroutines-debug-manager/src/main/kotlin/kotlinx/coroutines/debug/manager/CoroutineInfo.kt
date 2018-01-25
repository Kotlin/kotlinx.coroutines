package kotlinx.coroutines.debug.manager

private fun StackTraceElement.rename() =
        if (methodName == "doResume") StackTraceElement(className, "invoke", fileName, lineNumber)
        else this

// java.lang.Thread.getStackTrace(Thread.java:1559)
private val FRAMES_TO_REMOVE_FROM_ACTIVE_RUNNING_THREAD_WHEN_RUN = 1

// java.lang.Thread.getStackTrace(Thread.java:1559)
// kotlinx.coroutines.debug.manager.CoroutineSnapshot.<init>(CoroutineInfo.kt:26)
// kotlinx.coroutines.debug.manager.CoroutineStack.getSnapshot(CoroutineStack.kt:68)
// kotlinx.coroutines.debug.manager.StacksManager.getSnapshot(StacksManager.kt:49)
// kotlinx.coroutines.debug.manager.StacksManager.getFullDumpString(StacksManager.kt:56)

// sun.reflect.NativeMethodAccessorImpl.invoke0(Native Method)
// sun.reflect.NativeMethodAccessorImpl.invoke(NativeMethodAccessorImpl.java:62)
// sun.reflect.DelegatingMethodAccessorImpl.invoke(DelegatingMethodAccessorImpl.java:43)
// java.lang.reflect.Method.invoke(Method.java:498)
private val FRAMES_TO_REMOVE_FROM_ACTIVE_RUNNING_THREAD_WHEN_DEBUG = 5 + 4 //FIXME

data class CoroutineSnapshot(
        val name: String,
        val context: WrappedContext,
        val status: CoroutineStatus,
        val thread: Thread,
        val coroutineStack: List<MethodCall>) {
    val threadStack = thread.stackTrace.toList()
    fun coroutineInfo(calledFromThread: Thread, conf: Configuration) = when (status) {
        CoroutineStatus.Created -> CreatedCoroutineInfo(name, context.additionalInfo, thread)
        CoroutineStatus.Suspended -> {
            val suspendedAt = with(coroutineStack.first().method) { "$className.$name" }
            SuspendedCoroutineInfo(name, context.additionalInfo, suspendedAt, thread,
                    coroutineStack.dropLast(1).map { it.stackTraceElement.rename() })
        }
        CoroutineStatus.Running -> {
            val cleanThreadStack = removeInvokeBeforeDoResume(
                    if (calledFromThread == thread) threadStack.drop(conf.topFramesToDrop) else
                        threadStack)
            val firstCalls = suspendBlockFirstCalls(cleanThreadStack)
            require(firstCalls.size == StacksManager.coroutinesOnThread(thread).size)
            val annotatedStack = cleanThreadStack.map { it.rename() }.map { STEItem(it) }
                    .toMutableList<CoroutineStackViewElement>().apply {
                for ((index, coroutine) in StacksManager.coroutinesOnThread(thread).withIndex())
                    add(firstCalls[index], CoroutineInfoItem(coroutine.name, coroutine.name == name))
            }
            RunningCoroutineInfo(name, context.additionalInfo, thread, annotatedStack)
        }
    }
}

private fun removeInvokeBeforeDoResume(stack: List<StackTraceElement>): List<StackTraceElement> {
    val result = stack.toMutableList()
    var index = 0
    while (index < result.size) {
        if (isSuspendLambdaDoResume(result, index))
            result.removeAt(index + 1) //doResume will be renamed to deleted invoke
        index++
    }
    return result
}

private fun isSuspendLambdaDoResume(stack: List<StackTraceElement>, atDoResumeIndex: Int): Boolean {
    if (knownDoResumeFunctionsMap.values.none { it.equalsTo(stack[atDoResumeIndex]) }) return false
    val lambdaObjectClassName = stack[atDoResumeIndex].className
    if (atDoResumeIndex + 1 > stack.lastIndex
            || stack[atDoResumeIndex + 1].methodName != "invoke"
            || stack[atDoResumeIndex + 1].className != lambdaObjectClassName
            || stack[atDoResumeIndex + 1].lineNumber != -1) return false
    if (atDoResumeIndex + 2 > stack.lastIndex
            || stack[atDoResumeIndex + 2].methodName != "invoke"
            || stack[atDoResumeIndex + 2].className != lambdaObjectClassName) return false
    return atDoResumeIndex + 3 <= stack.lastIndex && allSuspendCallsMap.values.any {
        it.stackTraceElement == stack[atDoResumeIndex + 3] && it.method.name == "invoke"
    }
}

//doResume can be called only from invoke or other suspend function
private fun suspendBlockFirstCalls(stack: List<StackTraceElement>): List<Int> {
    val coroutineStarts = mutableListOf<Int>()
    var inCoroutine = false
    var index = stack.lastIndex
    while (index >= 0) {
        if (allSuspendCallsMap.values.any { it.stackTraceElement == stack[index] }
                || knownDoResumeFunctionsMap.values.any { it.equalsTo(stack[index]) }
                || (index - 1 > 0 && knownDoResumeFunctionsMap.values.any { it.equalsTo(stack[index - 1]) })
                || (stack[index].methodName == "invoke" && index - 1 > 0
                && knownDoResumeFunctionsMap.values.any { it.equalsTo(stack[index - 1]) })) {
            if (!inCoroutine) {
                coroutineStarts += index
                inCoroutine = true
            }
        } else
            inCoroutine = false
        index -= 1
    }
    return coroutineStarts
}

sealed class Configuration(val topFramesToDrop: Int) {
    object Run : Configuration(FRAMES_TO_REMOVE_FROM_ACTIVE_RUNNING_THREAD_WHEN_RUN)
    object Debug : Configuration(FRAMES_TO_REMOVE_FROM_ACTIVE_RUNNING_THREAD_WHEN_DEBUG)
}

data class FullCoroutineSnapshot(val coroutines: List<CoroutineSnapshot>) {
    fun fullCoroutineDump(runConfiguration: Configuration): FullCoroutineDump {
        val currentThread = Thread.currentThread()
        return FullCoroutineDump(coroutines.map { it.coroutineInfo(currentThread, runConfiguration) })
    }

    fun prettyPrint() = buildString {
        coroutines.forEach {
            append("${it.name} ${it.context.name} ${it.context.name} ${it.status} ${it.thread}\n")
            if (it.coroutineStack.isNotEmpty())
                append(it.coroutineStack.joinToString(separator = "\n", prefix = "coroutine stack:\n", postfix = "\n"))
            if (it.status != CoroutineStatus.Suspended && it.threadStack.isNotEmpty())
                append(it.threadStack.joinToString(separator = "\n", prefix = "thread stack:\n", postfix = "\n"))
            append("\n")
        }
    }
}

data class FullCoroutineDump(private val coroutines: List<CoroutineInfo>) {
    override fun toString() = buildString {
        append(currentTimePretty("yyyy-MM-dd HH:mm:ss")) //as in thread dump
        append(" Full coroutine dump\n")
        coroutines.forEach {
            append("$it\n")
        }
    }
}

sealed class CoroutineStackViewElement
data class STEItem(val ste: StackTraceElement) : CoroutineStackViewElement() {
    override fun toString() = "    at $ste"
}

data class CoroutineInfoItem(val coroutineName: String, val current: Boolean = false) : CoroutineStackViewElement() {
    override fun toString() = "    -- ^^ $coroutineName${if (current) " (current)" else ""} ^^"
}

sealed class CoroutineInfo {
    abstract val name: String
    abstract val additionalInfo: String
    abstract val status: CoroutineStatus
    abstract val thread: Thread
    abstract val labeledCurrentThreadStack: List<CoroutineStackViewElement>
    protected abstract fun header(): String
    protected abstract fun body(): String
    protected val firstLine: String
        get() = "\"$name\"${if (additionalInfo.isNotEmpty()) " $additionalInfo" else ""}\n"

    protected fun statusLine(info: String = "") = "  Status: $status${if (info.isNotEmpty()) " $info" else ""}\n"
    override fun toString() = buildString {
        append(header())
        append(body())
    }
}

data class CreatedCoroutineInfo(
        override val name: String,
        override val additionalInfo: String,
        override val thread: Thread
) : CoroutineInfo() {
    override val labeledCurrentThreadStack = emptyList<CoroutineStackViewElement>()
    override val status = CoroutineStatus.Created
    override fun header() = firstLine + statusLine("on $thread")
    override fun body() = ""
    override fun toString() = super.toString()
}

data class SuspendedCoroutineInfo(
        override val name: String,
        override val additionalInfo: String,
        val suspendedAt: String,
        override val thread: Thread,
        val realStack: List<StackTraceElement>
) : CoroutineInfo() {
    override val labeledCurrentThreadStack: List<CoroutineStackViewElement> = realStack.map { STEItem(it) }
    override val status = CoroutineStatus.Suspended
    override fun header() = firstLine + statusLine("at $suspendedAt")
    override fun body() = labeledCurrentThreadStack.joinToString(separator = "\n", postfix = "\n")
    override fun toString() = super.toString()
}

data class RunningCoroutineInfo(
        override val name: String,
        override val additionalInfo: String,
        override val thread: Thread,
        override val labeledCurrentThreadStack: List<CoroutineStackViewElement>
) : CoroutineInfo() {
    override val status = CoroutineStatus.Running
    override fun header() = firstLine + statusLine("on $thread")
    override fun body() = labeledCurrentThreadStack.joinToString(separator = "\n", postfix = "\n")
    override fun toString() = super.toString()
}