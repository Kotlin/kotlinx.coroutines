/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import net.bytebuddy.*
import net.bytebuddy.agent.*
import net.bytebuddy.dynamic.loading.*
import java.io.*
import java.text.*
import java.util.*
import kotlin.collections.ArrayList
import kotlin.collections.HashMap
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.*
import kotlinx.coroutines.internal.artificialFrame as createArtificialFrame // IDEA bug workaround

/**
 * Mirror of [DebugProbes] with actual implementation.
 * [DebugProbes] are implemented with pimpl to simplify user-facing class and make it look simple and
 * documented.
 */
internal object DebugProbesImpl {
    private const val ARTIFICIAL_FRAME_MESSAGE = "Coroutine creation stacktrace"
    private val dateFormat = SimpleDateFormat("yyyy/MM/dd HH:mm:ss")
    private val capturedCoroutines = HashSet<CoroutineOwner<*>>()
    @Volatile
    private var installations = 0
    internal val isInstalled: Boolean get() = installations > 0
    // To sort coroutines by creation order, used as unique id
    private var sequenceNumber: Long = 0

    /*
     * This is an optimization in the face of KT-29997:
     * Consider suspending call stack a()->b()->c() and c() completes its execution and every call is
     * "almost" in tail position.
     *
     * Then at least three RUNNING -> RUNNING transitions will occur consecutively and complexity of each is O(depth).
     * To avoid that quadratic complexity, we are caching lookup result for such chains in this map and update it incrementally.
     */
    private val callerInfoCache = HashMap<CoroutineStackFrame, CoroutineInfo>()

    @Synchronized
    public fun install() {
        if (++installations > 1) return

        ByteBuddyAgent.install()
        val cl = Class.forName("kotlin.coroutines.jvm.internal.DebugProbesKt")
        val cl2 = Class.forName("kotlinx.coroutines.debug.DebugProbesKt")

        ByteBuddy()
            .redefine(cl2)
            .name(cl.name)
            .make()
            .load(cl.classLoader, ClassReloadingStrategy.fromInstalledAgent())
    }

    @Synchronized
    public fun uninstall() {
        check(isInstalled) { "Agent was not installed" }
        if (--installations != 0) return

        capturedCoroutines.clear()
        callerInfoCache.clear()
        val cl = Class.forName("kotlin.coroutines.jvm.internal.DebugProbesKt")
        val cl2 = Class.forName("kotlinx.coroutines.debug.internal.NoOpProbesKt")

        ByteBuddy()
            .redefine(cl2)
            .name(cl.name)
            .make()
            .load(cl.classLoader, ClassReloadingStrategy.fromInstalledAgent())
    }

    @Synchronized
    public fun hierarchyToString(job: Job): String {
        check(isInstalled) { "Debug probes are not installed" }
        val jobToStack = capturedCoroutines
            .filter { it.delegate.context[Job] != null }
            .associateBy({ it.delegate.context[Job]!! }, { it.info })
        return buildString {
            job.build(jobToStack, this, "")
        }
    }

    private fun Job.build(map: Map<Job, CoroutineInfo>, builder: StringBuilder, indent: String) {
        val info = map[this]
        val newIndent: String
        if (info == null) { // Append coroutine without stacktrace
            // Do not print scoped coroutines and do not increase indentation level
            @Suppress("INVISIBLE_REFERENCE")
            if (this !is kotlinx.coroutines.internal.ScopeCoroutine<*>) {
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

    @Synchronized
    public fun dumpCoroutinesInfo(): List<CoroutineInfo> {
        check(isInstalled) { "Debug probes are not installed" }
        return capturedCoroutines.asSequence()
            .map { it.info.copy() } // Copy as CoroutineInfo can be mutated concurrently by DebugProbes
            .sortedBy { it.sequenceNumber }
            .toList()
    }

    public fun dumpCoroutines(out: PrintStream) = synchronized(out) {
        /*
         * This method synchronizes both on `out` and `this` for a reason:
         * 1) Synchronization on `this` is required to have a consistent snapshot of coroutines.
         * 2) Synchronization on `out` is not required, but prohibits interleaving with any other
         *    (asynchronous) attempt to write to this `out` (System.out by default).
         * Yet this prevents the progress of coroutines until they are fully dumped to the out which we find acceptable compromise.
         */
        dumpCoroutinesSynchronized(out)
    }

    @Synchronized
    private fun dumpCoroutinesSynchronized(out: PrintStream) {
        check(isInstalled) { "Debug probes are not installed" }
        out.print("Coroutines dump ${dateFormat.format(System.currentTimeMillis())}")
        capturedCoroutines
            .asSequence()
            .sortedBy { it.info.sequenceNumber }
            .forEach { owner ->
                val info = owner.info
                val observedStackTrace = info.lastObservedStackTrace()
                val enhancedStackTrace = enhanceStackTraceWithThreadDump(info, observedStackTrace)
                val state = if (info.state == State.RUNNING && enhancedStackTrace === observedStackTrace)
                    "${info.state} (Last suspension stacktrace, not an actual stacktrace)"
                else
                    info.state.toString()

                out.print("\n\nCoroutine ${owner.delegate}, state: $state")
                if (observedStackTrace.isEmpty()) {
                    out.print("\n\tat ${createArtificialFrame(ARTIFICIAL_FRAME_MESSAGE)}")
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

    /**
     * Tries to enhance [coroutineTrace] (obtained by call to [CoroutineInfo.lastObservedStackTrace]) with
     * thread dump of [CoroutineInfo.lastObservedThread].
     *
     * Returns [coroutineTrace] if enhancement was unsuccessful or the enhancement result.
     */
    private fun enhanceStackTraceWithThreadDump(
        info: CoroutineInfo,
        coroutineTrace: List<StackTraceElement>
    ): List<StackTraceElement> {
        val thread = info.lastObservedThread
        if (info.state != State.RUNNING || thread == null) return coroutineTrace
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

        val (continuationStartFrame, frameSkipped) = findContinuationStartIndex(
            indexOfResumeWith,
            actualTrace,
            coroutineTrace)

        if (continuationStartFrame == -1) return coroutineTrace

        val delta = if (frameSkipped) 1 else 0
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
     * Returns index of such frame (or -1) and flag indicating whether frame with state machine was skipped
     */
    private fun findContinuationStartIndex(
        indexOfResumeWith: Int,
        actualTrace: Array<StackTraceElement>,
        coroutineTrace: List<StackTraceElement>
    ): Pair<Int, Boolean> {
        val result = findIndexOfFrame(indexOfResumeWith - 1, actualTrace, coroutineTrace)
        if (result == -1) return findIndexOfFrame(indexOfResumeWith - 2, actualTrace, coroutineTrace) to true
        return result to false
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

    internal fun probeCoroutineResumed(frame: Continuation<*>) = updateState(frame, State.RUNNING)

    internal fun probeCoroutineSuspended(frame: Continuation<*>) = updateState(frame, State.SUSPENDED)

    private fun updateState(frame: Continuation<*>, state: State) {
        // KT-29997 is here only since 1.3.30
        if (state == State.RUNNING && KotlinVersion.CURRENT.isAtLeast(1, 3, 30)) {
            val stackFrame = frame as? CoroutineStackFrame ?: return
            updateRunningState(stackFrame, state)
            return
        }

        // Find ArtificialStackFrame of the coroutine
        val owner = frame.owner() ?: return
        updateState(owner, frame, state)
    }

    @Synchronized // See comment to callerInfoCache
    private fun updateRunningState(frame: CoroutineStackFrame, state: State) {
        if (!isInstalled) return
        // Lookup coroutine info in cache or by traversing stack frame
        val info: CoroutineInfo
        val cached = callerInfoCache.remove(frame)
        if (cached != null) {
            info = cached
        } else {
            info = frame.owner()?.info ?: return
            // Guard against improper implementations of CoroutineStackFrame and bugs in the compiler
            callerInfoCache.remove(info.lastObservedFrame?.realCaller())
        }

        info.updateState(state, frame as Continuation<*>)
        // Do not cache it for proxy-classes such as ScopeCoroutines
        val caller = frame.realCaller() ?: return
        callerInfoCache[caller] = info
    }

    private tailrec fun CoroutineStackFrame.realCaller(): CoroutineStackFrame? {
        val caller = callerFrame ?: return null
        return if (caller.getStackTraceElement() != null) caller else caller.realCaller()
    }

    @Synchronized
    private fun updateState(owner: CoroutineOwner<*>, frame: Continuation<*>, state: State) {
        if (!isInstalled) return
        owner.info.updateState(state, frame)
    }

    private fun Continuation<*>.owner(): CoroutineOwner<*>? = (this as? CoroutineStackFrame)?.owner()

    private tailrec fun CoroutineStackFrame.owner(): CoroutineOwner<*>? =
        if (this is CoroutineOwner<*>) this else callerFrame?.owner()

    internal fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> {
        if (!isInstalled) return completion
        /*
         * If completion already has an owner, it means that we are in scoped coroutine (coroutineScope, withContext etc.),
         * then piggyback on its already existing owner and do not replace completion
         */
        val owner = completion.owner()
        if (owner != null) return completion
        /*
         * Here we replace completion with a sequence of CoroutineStackFrame objects
         * which represents creation stacktrace, thus making stacktrace recovery mechanism
         * even more verbose (it will attach coroutine creation stacktrace to all exceptions),
         * and then using CoroutineOwner completion as unique identifier of coroutineSuspended/resumed calls.
         */
        val stacktrace = sanitizeStackTrace(Exception())
        val frame = stacktrace.foldRight<StackTraceElement, CoroutineStackFrame?>(null) { frame, acc ->
            object : CoroutineStackFrame {
                override val callerFrame: CoroutineStackFrame? = acc
                override fun getStackTraceElement(): StackTraceElement = frame
            }
        }!!

        return createOwner(completion, frame)
    }

    @Synchronized
    private fun <T> createOwner(completion: Continuation<T>, frame: CoroutineStackFrame): Continuation<T> {
        if (!isInstalled) return completion
        val info = CoroutineInfo(completion.context, frame, ++sequenceNumber)
        val owner = CoroutineOwner(completion, info, frame)
        capturedCoroutines += owner
        return owner
    }

    @Synchronized
    private fun probeCoroutineCompleted(owner: CoroutineOwner<*>) {
        capturedCoroutines.remove(owner)
        /*
         * This removal is a guard against improperly implemented CoroutineStackFrame
         * and bugs in the compiler.
         */
        val caller = owner.info.lastObservedFrame?.realCaller()
        callerInfoCache.remove(caller)
    }

    /**
     * This class is injected as completion of all continuations in [probeCoroutineCompleted].
     * It is owning the coroutine info and responsible for managing all its external info related to debug agent.
     */
    private class CoroutineOwner<T>(
        @JvmField val delegate: Continuation<T>,
        @JvmField val info: CoroutineInfo,
        frame: CoroutineStackFrame
    ) : Continuation<T> by delegate, CoroutineStackFrame by frame {
        override fun resumeWith(result: Result<T>) {
            probeCoroutineCompleted(this)
            delegate.resumeWith(result)
        }

        override fun toString(): String = delegate.toString()
    }

    private fun <T : Throwable> sanitizeStackTrace(throwable: T): List<StackTraceElement> {
        val stackTrace = throwable.stackTrace
        val size = stackTrace.size
        val probeIndex = stackTrace.indexOfLast { it.className == "kotlin.coroutines.jvm.internal.DebugProbesKt" }

        if (!DebugProbes.sanitizeStackTraces) {
            return List(size - probeIndex) {
                if (it == 0) createArtificialFrame(ARTIFICIAL_FRAME_MESSAGE) else stackTrace[it + probeIndex]
            }
        }

        /*
         * Trim intervals of internal methods from the stacktrace (bounds are excluded from trimming)
         * E.g. for sequence [e, i1, i2, i3, e, i4, e, i5, i6, e7]
         * output will be [e, i1, i3, e, i4, e, i5, i7]
         */
        val result = ArrayList<StackTraceElement>(size - probeIndex + 1)
        result += createArtificialFrame(ARTIFICIAL_FRAME_MESSAGE)
        var includeInternalFrame = true
        for (i in (probeIndex + 1) until size - 1) {
            val element = stackTrace[i]
            if (!element.isInternalMethod) {
                includeInternalFrame = true
                result += element
                continue
            }

            if (includeInternalFrame) {
                result += element
                includeInternalFrame = false
            } else if (stackTrace[i + 1].isInternalMethod) {
                continue
            } else {
                result += element
                includeInternalFrame = true
            }

        }

        result += stackTrace[size - 1]
        return result
    }

    private val StackTraceElement.isInternalMethod: Boolean get() = className.startsWith("kotlinx.coroutines")
}
