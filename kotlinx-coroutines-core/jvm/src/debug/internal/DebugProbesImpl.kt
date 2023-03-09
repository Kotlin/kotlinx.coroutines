/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.internal

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.ScopeCoroutine
import java.io.*
import java.lang.StackTraceElement
import java.text.*
import java.util.concurrent.locks.*
import kotlin.collections.ArrayList
import kotlin.concurrent.*
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.CoroutineStackFrame
import kotlin.synchronized
import _COROUTINE.ArtificialStackFrames

internal object DebugProbesImpl {
    private val ARTIFICIAL_FRAME = ArtificialStackFrames().coroutineCreation()
    private val dateFormat = SimpleDateFormat("yyyy/MM/dd HH:mm:ss")

    private var weakRefCleanerThread: Thread? = null

    // Values are boolean, so this map does not need to use a weak reference queue
    private val capturedCoroutinesMap = ConcurrentWeakMap<CoroutineOwner<*>, Boolean>()
    private val capturedCoroutines: Set<CoroutineOwner<*>> get() = capturedCoroutinesMap.keys

    private val installations = atomic(0)

    /**
     * This internal method is used by IDEA debugger under the JVM name of
     * "isInstalled$kotlinx_coroutines_debug".
     */
    internal val isInstalled: Boolean get() = installations.value > 0

    // To sort coroutines by creation order, used as unique id
    private val sequenceNumber = atomic(0L)

    public var sanitizeStackTraces: Boolean = true
    public var enableCreationStackTraces: Boolean = true

    /*
     * Substitute for service loader, DI between core and debug modules.
     * If the agent was installed via command line -javaagent parameter, do not use byte-buddy to avoid dynamic attach.
     */
    private val dynamicAttach = getDynamicAttach()

    @Suppress("UNCHECKED_CAST")
    private fun getDynamicAttach(): Function1<Boolean, Unit>? = runCatching {
        val clz = Class.forName("kotlinx.coroutines.debug.internal.ByteBuddyDynamicAttach")
        val ctor = clz.constructors[0]
        ctor.newInstance() as Function1<Boolean, Unit>
    }.getOrNull()

    /*
     * This is an optimization in the face of KT-29997:
     * Consider suspending call stack a()->b()->c() and c() completes its execution and every call is
     * "almost" in tail position.
     *
     * Then at least three RUNNING -> RUNNING transitions will occur consecutively and complexity of each is O(depth).
     * To avoid that quadratic complexity, we are caching lookup result for such chains in this map and update it incrementally.
     *
     * [DebugCoroutineInfoImpl] keeps a lot of auxiliary information about a coroutine, so we use a weak reference queue
     * to promptly release the corresponding memory when the reference to the coroutine itself was already collected.
     */
    private val callerInfoCache = ConcurrentWeakMap<CoroutineStackFrame, DebugCoroutineInfoImpl>(weakRefQueue = true)

    fun install() {
        if (installations.incrementAndGet() > 1) return
        startWeakRefCleanerThread()
        if (AgentInstallationType.isInstalledStatically) return
        dynamicAttach?.invoke(true) // attach
    }

    fun uninstall() {
        check(isInstalled) { "Agent was not installed" }
        if (installations.decrementAndGet() != 0) return
        stopWeakRefCleanerThread()
        capturedCoroutinesMap.clear()
        callerInfoCache.clear()
        if (AgentInstallationType.isInstalledStatically) return
        dynamicAttach?.invoke(false) // detach
    }

    private fun startWeakRefCleanerThread() {
        weakRefCleanerThread = thread(isDaemon = true, name = "Coroutines Debugger Cleaner") {
            callerInfoCache.runWeakRefQueueCleaningLoopUntilInterrupted()
        }
    }

    private fun stopWeakRefCleanerThread() {
        val thread = weakRefCleanerThread ?: return
        weakRefCleanerThread = null
        thread.interrupt()
        thread.join()
    }

    fun hierarchyToString(job: Job): String {
        check(isInstalled) { "Debug probes are not installed" }
        val jobToStack = capturedCoroutines
            .filter { it.delegate.context[Job] != null }
            .associateBy({ it.delegate.context.job }, { it.info })
        return buildString {
            job.build(jobToStack, this, "")
        }
    }

    private fun Job.build(map: Map<Job, DebugCoroutineInfoImpl>, builder: StringBuilder, indent: String) {
        val info = map[this]
        val newIndent: String
        if (info == null) { // Append coroutine without stacktrace
            // Do not print scoped coroutines and do not increase indentation level
            @Suppress("INVISIBLE_REFERENCE")
            if (this !is ScopeCoroutine<*>) {
                builder.append("$indent$debugString\n")
                newIndent = indent + "\t"
            } else {
                newIndent = indent
            }
        } else {
            // Append coroutine with its last stacktrace element
            val element = info.lastObservedStackTrace().firstOrNull()
            val state = info.state
            builder.append("$indent$debugString, continuation is $state at line $element\n")
            newIndent = indent + "\t"
        }
        // Append children with new indent
        for (child in children) {
            child.build(map, builder, newIndent)
        }
    }

    @Suppress("DEPRECATION_ERROR") // JobSupport
    private val Job.debugString: String get() = if (this is JobSupport) toDebugString() else toString()

    /**
     * Private method that dumps coroutines so that different public-facing method can use
     * to produce different result types.
     */
    private inline fun <R : Any> dumpCoroutinesInfoImpl(crossinline create: (CoroutineOwner<*>, CoroutineContext) -> R): List<R> {
        check(isInstalled) { "Debug probes are not installed" }
        return capturedCoroutines
            .asSequence()
            // Stable ordering of coroutines by their sequence number
            .sortedBy { it.info.sequenceNumber }
            // Leave in the dump only the coroutines that were not collected while we were dumping them
            .mapNotNull { owner ->
                // Fuse map and filter into one operation to save an inline
                if (owner.isFinished()) null
                else owner.info.context?.let { context -> create(owner, context) }
            }.toList()
    }

    /*
     * This method optimises the number of packages sent by the IDEA debugger
     * to a client VM to speed up fetching of coroutine information.
     *
     * The return value is an array of objects, which consists of four elements:
     * 1) A string in a JSON format that stores information that is needed to display
     *    every coroutine in the coroutine panel in the IDEA debugger.
     * 2) An array of last observed threads.
     * 3) An array of last observed frames.
     * 4) An array of DebugCoroutineInfo.
     *
     * ### Implementation note
     * For methods like `dumpCoroutinesInfo` JDWP provides `com.sun.jdi.ObjectReference`
     * that does a roundtrip to client VM for *each* field or property read.
     * To avoid that, we serialize most of the critical for UI data into a primitives
     * to save an exponential number of roundtrips.
     *
     * Internal (JVM-public) method used by IDEA debugger as of 1.6.0-RC.
     */
    @OptIn(ExperimentalStdlibApi::class)
    public fun dumpCoroutinesInfoAsJsonAndReferences(): Array<Any> {
        val coroutinesInfo = dumpCoroutinesInfo()
        val size = coroutinesInfo.size
        val lastObservedThreads = ArrayList<Thread?>(size)
        val lastObservedFrames = ArrayList<CoroutineStackFrame?>(size)
        val coroutinesInfoAsJson = ArrayList<String>(size)
        for (info in coroutinesInfo) {
            val context = info.context
            val name = context[CoroutineName.Key]?.name?.toStringWithQuotes()
            val dispatcher = context[CoroutineDispatcher.Key]?.toStringWithQuotes()
            coroutinesInfoAsJson.add(
                """
                {
                    "name": $name,
                    "id": ${context[CoroutineId.Key]?.id},
                    "dispatcher": $dispatcher,
                    "sequenceNumber": ${info.sequenceNumber},
                    "state": "${info.state}"
                } 
                """.trimIndent()
            )
            lastObservedFrames.add(info.lastObservedFrame)
            lastObservedThreads.add(info.lastObservedThread)
        }

        return arrayOf(
            "[${coroutinesInfoAsJson.joinToString()}]",
            lastObservedThreads.toTypedArray(),
            lastObservedFrames.toTypedArray(),
            coroutinesInfo.toTypedArray()
        )
    }

    /*
     * Internal (JVM-public) method used by IDEA debugger as of 1.6.0-RC.
     */
    public fun enhanceStackTraceWithThreadDumpAsJson(info: DebugCoroutineInfo): String {
        val stackTraceElements = enhanceStackTraceWithThreadDump(info, info.lastObservedStackTrace)
        val stackTraceElementsInfoAsJson = mutableListOf<String>()
        for (element in stackTraceElements) {
            stackTraceElementsInfoAsJson.add(
                """
                {
                    "declaringClass": "${element.className}",
                    "methodName": "${element.methodName}",
                    "fileName": ${element.fileName?.toStringWithQuotes()},
                    "lineNumber": ${element.lineNumber}
                }
                """.trimIndent()
            )
        }

        return "[${stackTraceElementsInfoAsJson.joinToString()}]"
    }

    private fun Any.toStringWithQuotes() = "\"$this\""

    /*
     * Internal (JVM-public) method used by IDEA debugger as of 1.4-M3.
     */
    public fun dumpCoroutinesInfo(): List<DebugCoroutineInfo> =
        dumpCoroutinesInfoImpl { owner, context -> DebugCoroutineInfo(owner.info, context) }

    /*
     * Internal (JVM-public) method to be used by IDEA debugger in the future (not used as of 1.4-M3).
     * It is equivalent to [dumpCoroutinesInfo], but returns serializable (and thus less typed) objects.
     */
    public fun dumpDebuggerInfo(): List<DebuggerInfo> =
        dumpCoroutinesInfoImpl { owner, context -> DebuggerInfo(owner.info, context) }

    public fun dumpCoroutines(out: PrintStream): Unit = synchronized(out) {
        /*
         * This method synchronizes both on `out` and `this` for a reason:
         * 1) Taking a write lock is required to have a consistent snapshot of coroutines.
         * 2) Synchronization on `out` is not required, but prohibits interleaving with any other
         *    (asynchronous) attempt to write to this `out` (System.out by default).
         * Yet this prevents the progress of coroutines until they are fully dumped to the out which we find acceptable compromise.
         */
        dumpCoroutinesSynchronized(out)
    }

    /*
     * Filters out coroutines that do not call probeCoroutineCompleted,
     * are completed, but not yet garbage collected.
     *
     * Typically, we intercept completion of the coroutine so it invokes "probeCoroutineCompleted",
     * but it's not the case for lazy coroutines that get cancelled before start.
     */
    private fun CoroutineOwner<*>.isFinished(): Boolean {
        // Guarded by lock
        val job = info.context?.get(Job) ?: return false
        if (!job.isCompleted) return false
        capturedCoroutinesMap.remove(this) // Clean it up by the way
        return true
    }

    private fun dumpCoroutinesSynchronized(out: PrintStream) {
        check(isInstalled) { "Debug probes are not installed" }
        out.print("Coroutines dump ${dateFormat.format(System.currentTimeMillis())}")
        capturedCoroutines
            .asSequence()
            .filter { !it.isFinished() }
            .sortedBy { it.info.sequenceNumber }
            .forEach { owner ->
                val info = owner.info
                val observedStackTrace = info.lastObservedStackTrace()
                val enhancedStackTrace = enhanceStackTraceWithThreadDumpImpl(info.state, info.lastObservedThread, observedStackTrace)
                val state = if (info.state == RUNNING && enhancedStackTrace === observedStackTrace)
                    "${info.state} (Last suspension stacktrace, not an actual stacktrace)"
                else
                    info.state
                out.print("\n\nCoroutine ${owner.delegate}, state: $state")
                if (observedStackTrace.isEmpty()) {
                    out.print("\n\tat $ARTIFICIAL_FRAME")
                    printStackTrace(out, info.creationStackTrace)
                } else {
                    printStackTrace(out, enhancedStackTrace)
                }
            }
    }

    private fun printStackTrace(out: PrintStream, frames: List<StackTraceElement>) {
        frames.forEach { frame ->
            out.print("\n\tat $frame")
        }
    }

    /*
     * Internal (JVM-public) method used by IDEA debugger as of 1.4-M3.
     * It is similar to [enhanceStackTraceWithThreadDumpImpl], but uses debugger-facing [DebugCoroutineInfo] type.
     */
    @Suppress("unused")
    public fun enhanceStackTraceWithThreadDump(
        info: DebugCoroutineInfo,
        coroutineTrace: List<StackTraceElement>
    ): List<StackTraceElement> =
        enhanceStackTraceWithThreadDumpImpl(info.state, info.lastObservedThread, coroutineTrace)

    /**
     * Tries to enhance [coroutineTrace] (obtained by call to [DebugCoroutineInfoImpl.lastObservedStackTrace]) with
     * thread dump of [DebugCoroutineInfoImpl.lastObservedThread].
     *
     * Returns [coroutineTrace] if enhancement was unsuccessful or the enhancement result.
     */
    private fun enhanceStackTraceWithThreadDumpImpl(
        state: String,
        thread: Thread?,
        coroutineTrace: List<StackTraceElement>
    ): List<StackTraceElement> {
        if (state != RUNNING || thread == null) return coroutineTrace
        // Avoid security manager issues
        val actualTrace = runCatching { thread.stackTrace }.getOrNull()
            ?: return coroutineTrace

        /*
         * Here goes heuristic that tries to merge two stacktraces: real one
         * (that has at least one but usually not so many suspend function frames)
         * and coroutine one that has only suspend function frames.
         *
         * Heuristic:
         * 1) Dump lastObservedThread
         * 2) Find the next frame after BaseContinuationImpl.resumeWith (continuation machinery).
         *   Invariant: this method is called under the lock, so such method **should** be present
         *   in continuation stacktrace.
         * 3) Find target method in continuation stacktrace (metadata-based)
         * 4) Prepend dumped stacktrace (trimmed by target frame) to continuation stacktrace
         *
         * Heuristic may fail on recursion and overloads, but it will be automatically improved
         * with KT-29997.
         */
        val indexOfResumeWith = actualTrace.indexOfFirst {
            it.className == "kotlin.coroutines.jvm.internal.BaseContinuationImpl" &&
                    it.methodName == "resumeWith" &&
                    it.fileName == "ContinuationImpl.kt"
        }

        val (continuationStartFrame, delta) = findContinuationStartIndex(
            indexOfResumeWith,
            actualTrace,
            coroutineTrace
        )

        if (continuationStartFrame == -1) return coroutineTrace

        val expectedSize = indexOfResumeWith + coroutineTrace.size - continuationStartFrame - 1 - delta
        val result = ArrayList<StackTraceElement>(expectedSize)
        for (index in 0 until indexOfResumeWith - delta) {
            result += actualTrace[index]
        }

        for (index in continuationStartFrame + 1 until coroutineTrace.size) {
            result += coroutineTrace[index]
        }

        return result
    }

    /**
     * Tries to find the lowest meaningful frame above `resumeWith` in the real stacktrace and
     * its match in a coroutines stacktrace (steps 2-3 in heuristic).
     *
     * This method does more than just matching `realTrace.indexOf(resumeWith) - 1`:
     * If method above `resumeWith` has no line number (thus it is `stateMachine.invokeSuspend`),
     * it's skipped and attempt to match next one is made because state machine could have been missing in the original coroutine stacktrace.
     *
     * Returns index of such frame (or -1) and number of skipped frames (up to 2, for state machine and for access$).
     */
    private fun findContinuationStartIndex(
        indexOfResumeWith: Int,
        actualTrace: Array<StackTraceElement>,
        coroutineTrace: List<StackTraceElement>
    ): Pair<Int, Int> {
        /*
         * Since Kotlin 1.5.0 we have these access$ methods that we have to skip.
         * So we have to test next frame for invokeSuspend, for $access and for actual suspending call.
         */
        repeat(3) {
            val result = findIndexOfFrame(indexOfResumeWith - 1 - it, actualTrace, coroutineTrace)
            if (result != -1) return result to it
        }
        return -1 to 0
    }

    private fun findIndexOfFrame(
        frameIndex: Int,
        actualTrace: Array<StackTraceElement>,
        coroutineTrace: List<StackTraceElement>
    ): Int {
        val continuationFrame = actualTrace.getOrNull(frameIndex)
            ?: return -1

        return coroutineTrace.indexOfFirst {
            it.fileName == continuationFrame.fileName &&
                    it.className == continuationFrame.className &&
                    it.methodName == continuationFrame.methodName
        }
    }

    internal fun probeCoroutineResumed(frame: Continuation<*>) = updateState(frame, RUNNING)

    internal fun probeCoroutineSuspended(frame: Continuation<*>) = updateState(frame, SUSPENDED)

    private fun updateState(frame: Continuation<*>, state: String) {
        if (!isInstalled) return
        // KT-29997 is here only since 1.3.30
        if (state == RUNNING && KotlinVersion.CURRENT.isAtLeast(1, 3, 30)) {
            val stackFrame = frame as? CoroutineStackFrame ?: return
            updateRunningState(stackFrame, state)
            return
        }

        // Find ArtificialStackFrame of the coroutine
        val owner = frame.owner() ?: return
        updateState(owner, frame, state)
    }

    // See comment to callerInfoCache
    private fun updateRunningState(frame: CoroutineStackFrame, state: String) {
        if (!isInstalled) return
        // Lookup coroutine info in cache or by traversing stack frame
        val info: DebugCoroutineInfoImpl
        val cached = callerInfoCache.remove(frame)
        val shouldBeMatchedWithProbeSuspended: Boolean
        if (cached != null) {
            info = cached
            shouldBeMatchedWithProbeSuspended = false
        } else {
            info = frame.owner()?.info ?: return
            shouldBeMatchedWithProbeSuspended = true
            // Guard against improper implementations of CoroutineStackFrame and bugs in the compiler
            val realCaller = info.lastObservedFrame?.realCaller()
            if (realCaller != null) callerInfoCache.remove(realCaller)
        }
        info.updateState(state, frame as Continuation<*>, shouldBeMatchedWithProbeSuspended)
        // Do not cache it for proxy-classes such as ScopeCoroutines
        val caller = frame.realCaller() ?: return
        callerInfoCache[caller] = info
    }

    private tailrec fun CoroutineStackFrame.realCaller(): CoroutineStackFrame? {
        val caller = callerFrame ?: return null
        return if (caller.getStackTraceElement() != null) caller else caller.realCaller()
    }

    private fun updateState(owner: CoroutineOwner<*>, frame: Continuation<*>, state: String) {
        if (!isInstalled) return
        owner.info.updateState(state, frame, true)
    }

    private fun Continuation<*>.owner(): CoroutineOwner<*>? = (this as? CoroutineStackFrame)?.owner()

    private tailrec fun CoroutineStackFrame.owner(): CoroutineOwner<*>? =
        if (this is CoroutineOwner<*>) this else callerFrame?.owner()

    // Not guarded by the lock at all, does not really affect consistency
    internal fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> {
        if (!isInstalled) return completion
        /*
         * If completion already has an owner, it means that we are in scoped coroutine (coroutineScope, withContext etc.),
         * then piggyback on its already existing owner and do not replace completion
         */
        val owner = completion.owner()
        if (owner != null) return completion
        /*
         * Here we replace completion with a sequence of StackTraceFrame objects
         * which represents creation stacktrace, thus making stacktrace recovery mechanism
         * even more verbose (it will attach coroutine creation stacktrace to all exceptions),
         * and then using CoroutineOwner completion as unique identifier of coroutineSuspended/resumed calls.
         */
        val frame = if (enableCreationStackTraces) {
            sanitizeStackTrace(Exception()).toStackTraceFrame()
        } else {
            null
        }
        return createOwner(completion, frame)
    }

    private fun List<StackTraceElement>.toStackTraceFrame(): StackTraceFrame =
        StackTraceFrame(
            foldRight<StackTraceElement, StackTraceFrame?>(null) { frame, acc ->
                StackTraceFrame(acc, frame)
            }, ARTIFICIAL_FRAME
        )

    private fun <T> createOwner(completion: Continuation<T>, frame: StackTraceFrame?): Continuation<T> {
        if (!isInstalled) return completion
        val info = DebugCoroutineInfoImpl(completion.context, frame, sequenceNumber.incrementAndGet())
        val owner = CoroutineOwner(completion, info)
        capturedCoroutinesMap[owner] = true
        if (!isInstalled) capturedCoroutinesMap.clear()
        return owner
    }

    // Not guarded by the lock at all, does not really affect consistency
    private fun probeCoroutineCompleted(owner: CoroutineOwner<*>) {
        capturedCoroutinesMap.remove(owner)
        /*
         * This removal is a guard against improperly implemented CoroutineStackFrame
         * and bugs in the compiler.
         */
        val caller = owner.info.lastObservedFrame?.realCaller() ?: return
        callerInfoCache.remove(caller)
    }

    /**
     * This class is injected as completion of all continuations in [probeCoroutineCompleted].
     * It is owning the coroutine info and responsible for managing all its external info related to debug agent.
     */
    private class CoroutineOwner<T>(
        @JvmField val delegate: Continuation<T>,
        @JvmField val info: DebugCoroutineInfoImpl
    ) : Continuation<T> by delegate, CoroutineStackFrame {
        private val frame get() = info.creationStackBottom

        override val callerFrame: CoroutineStackFrame?
            get() = frame?.callerFrame

        override fun getStackTraceElement(): StackTraceElement? = frame?.getStackTraceElement()

        override fun resumeWith(result: Result<T>) {
            probeCoroutineCompleted(this)
            delegate.resumeWith(result)
        }

        override fun toString(): String = delegate.toString()
    }

    private fun <T : Throwable> sanitizeStackTrace(throwable: T): List<StackTraceElement> {
        val stackTrace = throwable.stackTrace
        val size = stackTrace.size
        val traceStart = 1 + stackTrace.indexOfLast { it.className == "kotlin.coroutines.jvm.internal.DebugProbesKt" }

        if (!sanitizeStackTraces) {
            return List(size - traceStart) { stackTrace[it + traceStart] }
        }

        /*
         * Trim intervals of internal methods from the stacktrace (bounds are excluded from trimming)
         * E.g. for sequence [e, i1, i2, i3, e, i4, e, i5, i6, i7]
         * output will be [e, i1, i3, e, i4, e, i5, i7]
         *
         * If an interval of internal methods ends in a synthetic method, the outermost non-synthetic method in that
         * interval will also be included.
         */
        val result = ArrayList<StackTraceElement>(size - traceStart + 1)
        var i = traceStart
        while (i < size) {
            if (stackTrace[i].isInternalMethod) {
                result += stackTrace[i] // we include the boundary of the span in any case
                // first index past the end of the span of internal methods that starts from `i`
                var j = i + 1
                while (j < size && stackTrace[j].isInternalMethod) {
                    ++j
                }
                // index of the last non-synthetic internal methods in this span, or `i` if there are no such methods
                var k = j - 1
                while (k > i && stackTrace[k].fileName == null) {
                    k -= 1
                }
                if (k > i && k < j - 1) {
                    /* there are synthetic internal methods at the end of this span, but there is a non-synthetic method
                    after `i`, so we include it. */
                    result += stackTrace[k]
                }
                result += stackTrace[j - 1] // we include the other boundary of this span in any case, too
                i = j
            } else {
                result += stackTrace[i]
                ++i
            }
        }
        return result
    }

    private val StackTraceElement.isInternalMethod: Boolean get() = className.startsWith("kotlinx.coroutines")
}
