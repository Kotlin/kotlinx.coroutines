package kotlinx.coroutines.debug.manager

import java.lang.ref.ReferenceQueue
import java.lang.ref.WeakReference
import java.util.*
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.CopyOnWriteArrayList
import kotlin.coroutines.experimental.Continuation

val DEBUG_AGENT_PACKAGE_PREFIX = "kotlinx.coroutines.debug"

private fun classNameBasedKey(currentClassName: String, index: Int) = "${currentClassName}___$index"

private fun Collection<String>.lastIndexForClassName(name: String) =
        filter { it.startsWith("${name}___") }.map { it.split("___").last().toInt() }.max()

val allSuspendCallsMap = ConcurrentHashMap<String, SuspendCall>()

val knownDoResumeFunctionsMap = ConcurrentHashMap<String, MethodId>()

fun <T> MutableMap<String, T>.classNameIndexedPut(className: String, data: T) =
        classNameBasedKey(className, (keys.lastIndexForClassName(className) ?: -1) + 1).also {
            put(it, data)
        }

enum class StackChangedEvent { Created, Suspended, Removed, WakedUp }

typealias OnStackChangedCallback = StacksManager.(StackChangedEvent, WrappedContext) -> Unit

private val referenceQueue = ReferenceQueue<Any?>()

open class WeakId<T : Any>(value: T) : WeakReference<T>(value, referenceQueue) {
    private val hash = System.identityHashCode(value)
    val value: T? get() = get()
    override fun equals(other: Any?): Boolean = this === other || other is WeakId<*> && get() === other.get()
    override fun hashCode() = hash
    override fun toString() = value
            ?.let { "${this::class.java.simpleName}(${it::class.java.name}@${it.prettyHash})" }
            ?: "${this::class.java.simpleName}(collected)"
}

typealias WeakContinuation = WeakId<out Continuation<Any?>>
typealias WeakWrappedCompletion = WeakId<WrappedCompletion>

object StacksManager {
    private val stackByContext = ConcurrentHashMap<WrappedContext, CoroutineStack>()
    private val stackByTopDoResumeContinuation = ConcurrentHashMap<WeakContinuation, CoroutineStack>()
    private val stacksByRunningThread = ConcurrentHashMap<Thread, MutableList<CoroutineStack>>()
    private val stackByInitialCompletion = ConcurrentHashMap<WeakWrappedCompletion, CoroutineStack>()
    private val ignoreDoResumeWithCompletion: MutableSet<WeakContinuation> =
            Collections.newSetFromMap(ConcurrentHashMap<WeakContinuation, Boolean>())

    private val onChangeCallbacks = CopyOnWriteArrayList<OnStackChangedCallback>()

    fun addOnStackChangedCallback(callback: OnStackChangedCallback) = onChangeCallbacks.add(callback)

    fun removeOnStackChangedCallback(callback: OnStackChangedCallback) = onChangeCallbacks.remove(callback)

    fun coroutinesOnThread(thread: Thread) = stacksByRunningThread[thread]?.toList().orEmpty()

    private fun cleanupOutdatedStacks() {
        while (true) {
            cleanup((referenceQueue.poll() ?: return) as WeakId)
        }
    }

    private fun cleanup(weakContinuation: WeakId<*>) {
        val stack = stackByInitialCompletion[weakContinuation] ?:
                stackByTopDoResumeContinuation[weakContinuation] ?: return
        debug { "cleanup(${weakContinuation.prettyHash})" }
        stackByContext.remove(stack.context)
        stackByTopDoResumeContinuation.remove(stack.topFrameCompletion)
        stackByInitialCompletion.remove(stack.initialCompletion)
        ignoreDoResumeWithCompletion.remove(weakContinuation) //should already be removed anyway
    }

    @JvmStatic
    fun getSnapshot(): FullCoroutineSnapshot {
        cleanupOutdatedStacks()
        return FullCoroutineSnapshot(stackByContext.values.map { it.getSnapshot() }.toList())
    }

    /**
     * Should only be called from debugger inside idea plugin
     */
    @JvmStatic
    @Suppress("unused")
    fun getFullDumpString() = getSnapshot().fullCoroutineDump(Configuration.Debug).toString()

    fun ignoreNextDoResume(completion: Continuation<Any?>) =
            ignoreDoResumeWithCompletion.add(WeakId(completion))

    fun handleNewCoroutineCreated(initialCompletion: WrappedCompletion) {
        cleanupOutdatedStacks()
        debug { "handleNewCoroutineCreated(${initialCompletion.prettyHash})" }
        val stack = CoroutineStack(WeakWrappedCompletion(initialCompletion))
        stackByContext[stack.context] = stack
        stackByInitialCompletion[stack.initialCompletion] = stack
        fireCallbacks(StackChangedEvent.Created, stack.context)
    }

    fun handleCoroutineExit(initialCompletion: WrappedCompletion) {
        debug { "handleCoroutineExit(${initialCompletion.prettyHash})" }
        val stack = stackByInitialCompletion.remove(WeakWrappedCompletion(initialCompletion)) ?: run {
            error { "Exiting missing coroutine $initialCompletion @${initialCompletion.prettyHash}) (completed twice?)" }
            return
        }
        stackByContext.remove(stack.context)
        stacksByRunningThread[stack.thread]?.let {
            it.remove(stack)
            if (it.isEmpty()) stacksByRunningThread.remove(stack.thread)
        }
        fireCallbacks(StackChangedEvent.Removed, stack.context)
    }

    fun handleAfterSuspendFunctionReturn(continuation: Continuation<Any?>, call: SuspendCall) {
        debug { "handleAfterSuspendFunctionReturn(${continuation.prettyHash}, $call)" }
        val runningOnCurrentThread = stacksByRunningThread[Thread.currentThread()]!!
        val stack = runningOnCurrentThread.last()
        stackByTopDoResumeContinuation.remove(stack.topFrameCompletion)
        if (stack.handleSuspendFunctionReturn(continuation, call)) {
            runningOnCurrentThread.dropLastInplace()
            stackByTopDoResumeContinuation[stack.topFrameCompletion] = stack
            fireCallbacks(StackChangedEvent.Suspended, stack.context)
            // todo: wakeup waiting handleDoResumeEnter
        }
    }

    fun handleDoResumeEnter(completion: Continuation<Any?>, continuation: Continuation<Any?>, function: MethodId) {
        fun message() = "handleDoResumeEnter(compl: ${completion.prettyHash}, cont: ${continuation.prettyHash}, $function)"
        if (ignoreDoResumeWithCompletion.remove(WeakId(completion))) {
            debug { message() + " - ignored" }
            return
        }
        // todo: how can we make it last check?
        stackByTopDoResumeContinuation.remove(WeakId(continuation))?.let {
            //first case: coroutine wake up
            debug { message() + " - coroutine waking up" }
            val previousStatus = it.status
            stackByTopDoResumeContinuation[it.handleDoResume(completion, continuation, function)] = it
            with(stacksByRunningThread.getOrPut(it.thread, { mutableListOf() })) { if (lastOrNull() != it) add(it) }
            if (previousStatus != CoroutineStatus.Running)
                fireCallbacks(StackChangedEvent.WakedUp, it.context)
            return
        }
        if (completion is WrappedCompletion) {
            //second case: first lambda for coroutine
            debug { message() + " - first lambda for coroutine" }
            val stack = stackByInitialCompletion[WeakId(completion)]!!
            stackByTopDoResumeContinuation[stack.handleDoResume(completion, continuation, function)] = stack
            stacksByRunningThread.getOrPut(stack.thread, { mutableListOf() }).add(stack)
            return
        }
        //final case: any lambda body call -> do nothing
        debug { message() + " - lambda body call" }
    }

    fun reset() {
        stackByContext.clear()
        stackByInitialCompletion.clear()
        stackByTopDoResumeContinuation.clear()
        stacksByRunningThread.clear()
        ignoreDoResumeWithCompletion.clear()
        onChangeCallbacks.clear()
    }

    private fun fireCallbacks(event: StackChangedEvent, context: WrappedContext) =
            onChangeCallbacks.forEach { it.invoke(this, event, context) }
}

private fun MutableList<*>.dropLastInplace() {
    if (isNotEmpty())
        removeAt(lastIndex)
}
