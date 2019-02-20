/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.*
import kotlinx.coroutines.internal.artificialFrame
import net.bytebuddy.*
import net.bytebuddy.agent.*
import net.bytebuddy.dynamic.loading.*
import java.io.*
import java.text.*
import java.util.*
import kotlin.collections.ArrayList
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.*

/**
 * Mirror of [DebugProbes] with actual implementation.
 * [DebugProbes] are implemented with pimpl to simplify user-facing class and make it look simple and
 * documented.
 */
internal object DebugProbesImpl {
    private const val ARTIFICIAL_FRAME_MESSAGE = "Coroutine creation stacktrace"
    private val dateFormat = SimpleDateFormat("yyyy/MM/dd HH:mm:ss")
    private val capturedCoroutines = WeakHashMap<ArtificialStackFrame<*>, CoroutineState>()
    @Volatile
    private var installations = 0
    private val isInstalled: Boolean get() = installations > 0
    // To sort coroutines by creation order, used as unique id
    private var sequenceNumber: Long = 0

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
            .filterKeys { it.delegate.context[Job] != null }
            .mapKeys { it.key.delegate.context[Job]!! }
        return buildString {
            job.build(jobToStack, this, "")
        }
    }

    private fun Job.build(map: Map<Job, CoroutineState>, builder: StringBuilder, indent: String) {
        val state = map[this]
        val newIndent: String
        if (state == null) { // Append coroutine without stacktrace
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
            val element = state.lastObservedStackTrace().firstOrNull()
            val contState = state.state
            builder.append("$indent$debugString, continuation is $contState at line $element\n")
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
    public fun dumpCoroutinesState(): List<CoroutineState> {
        check(isInstalled) { "Debug probes are not installed" }
        return capturedCoroutines.entries.asSequence()
            .map { CoroutineState(it.key.delegate, it.value) }
            .sortedBy { it.sequenceNumber }
            .toList()
    }

    public fun dumpCoroutines(out: PrintStream) {
        check(isInstalled) { "Debug probes are not installed" }
        // Avoid inference with other out/err invocations by creating a string first
        dumpCoroutines().let { out.println(it) }
    }

    @Synchronized
    private fun dumpCoroutines(): String = buildString {
        // Synchronization window can be reduce even more, but no need to do it here
        append("Coroutines dump ${dateFormat.format(System.currentTimeMillis())}")
        capturedCoroutines
            .asSequence()
            .sortedBy { it.value.sequenceNumber }
            .forEach { (key, value) ->
                val observedStackTrace = value.lastObservedStackTrace()
                val enhancedStackTrace = enhanceStackTraceWithThreadDump(value, observedStackTrace)
                val state = if (value.state == State.RUNNING && enhancedStackTrace === observedStackTrace)
                    "${value.state} (Last suspension stacktrace, not an actual stacktrace)"
                else
                    value.state.toString()

                append("\n\nCoroutine $key, state: $state")
                if (observedStackTrace.isEmpty()) {
                    append("\n\tat ${artificialFrame(ARTIFICIAL_FRAME_MESSAGE)}")
                    printStackTrace(value.creationStackTrace)
                } else {
                    printStackTrace(enhancedStackTrace)
                }
            }
    }

    /**
     * Tries to enhance [coroutineTrace] (obtained by call to [CoroutineState.lastObservedStackTrace]) with
     * thread dump of [CoroutineState.lastObservedThread].
     *
     * Returns [coroutineTrace] if enhancement was unsuccessful or the enhancement result.
     */
    private fun enhanceStackTraceWithThreadDump(
        state: CoroutineState,
        coroutineTrace: List<StackTraceElement>
    ): List<StackTraceElement> {
        val thread = state.lastObservedThread
        if (state.state != State.RUNNING || thread == null) return coroutineTrace
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
         *
         * 3) Find target method in continuation stacktrace (metadata-based)
         * 4) Prepend dumped stacktrace (trimmed by target frame) to continuation stacktrace
         *
         * Heuristic may fail on recursion and overloads, but it will be automatically improved
         * with KT-29997
         */
        val indexOfResumeWith = actualTrace.indexOfFirst {
            it.className == "kotlin.coroutines.jvm.internal.BaseContinuationImpl" &&
                    it.methodName == "resumeWith" &&
                    it.fileName == "ContinuationImpl.kt"
        }

        // We haven't found "BaseContinuationImpl.resumeWith" resume call in stacktrace
        // This is some inconsistency in machinery, do not fail, fallback
        val continuationFrame = actualTrace.getOrNull(indexOfResumeWith - 1)
            ?: return coroutineTrace

        val continuationStartFrame = coroutineTrace.indexOfFirst {
            it.fileName == continuationFrame.fileName &&
                    it.className == continuationFrame.className &&
                    it.methodName == continuationFrame.methodName
        } + 1

        if (continuationStartFrame == 0) return coroutineTrace

        val expectedSize = indexOfResumeWith + coroutineTrace.size - continuationStartFrame
        val result = ArrayList<StackTraceElement>(expectedSize)

        for (index in 0 until indexOfResumeWith) {
            result += actualTrace[index]
        }

        for (index in continuationStartFrame until coroutineTrace.size) {
            result += coroutineTrace[index]
        }

        return result
    }

    private fun StringBuilder.printStackTrace(frames: List<StackTraceElement>) {
        frames.forEach { frame ->
            append("\n\tat $frame")
        }
    }

    internal fun probeCoroutineResumed(frame: Continuation<*>) = updateState(frame, State.RUNNING)

    internal fun probeCoroutineSuspended(frame: Continuation<*>) = updateState(frame, State.SUSPENDED)

    private fun updateState(frame: Continuation<*>, state: State) {
        if (!isInstalled) return
        // Find ArtificialStackFrame of the coroutine
        val owner = frame.owner()
        updateState(owner, frame, state)
    }

    @Synchronized
    private fun updateState(owner: ArtificialStackFrame<*>?, frame: Continuation<*>, state: State) {
        val coroutineState = capturedCoroutines[owner] ?: return
        coroutineState.updateState(state, frame)
    }

    private fun Continuation<*>.owner(): ArtificialStackFrame<*>? =
        (this as? CoroutineStackFrame)?.owner()

    private tailrec fun CoroutineStackFrame.owner(): ArtificialStackFrame<*>? =
        if (this is ArtificialStackFrame<*>) this else callerFrame?.owner()

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
         * and then using this artificial frame as an identifier of coroutineSuspended/resumed calls.
         */
        val stacktrace = sanitizeStackTrace(Exception())
        val frame = stacktrace.foldRight<StackTraceElement, CoroutineStackFrame?>(null) { frame, acc ->
            object : CoroutineStackFrame {
                override val callerFrame: CoroutineStackFrame? = acc
                override fun getStackTraceElement(): StackTraceElement = frame
            }
        }
        return ArtificialStackFrame(completion, frame!!).also {
            storeFrame(it, completion)
        }
    }

    @Synchronized
    private fun <T> storeFrame(frame: ArtificialStackFrame<T>, completion: Continuation<T>) {
        capturedCoroutines[frame] = CoroutineState(completion, frame, ++sequenceNumber)
    }

    @Synchronized
    private fun probeCoroutineCompleted(coroutine: ArtificialStackFrame<*>) {
        capturedCoroutines.remove(coroutine)
    }

    private class ArtificialStackFrame<T>(
        @JvmField val delegate: Continuation<T>,
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
        val probeIndex = stackTrace.indexOfLast { it.className ==  "kotlin.coroutines.jvm.internal.DebugProbesKt" }

        if (!DebugProbes.sanitizeStackTraces) {
            return List(size - probeIndex) {
                if (it == 0) artificialFrame(ARTIFICIAL_FRAME_MESSAGE) else stackTrace[it + probeIndex]
            }
        }

        /*
         * Trim intervals of internal methods from the stacktrace (bounds are excluded from trimming)
         * E.g. for sequence [e, i1, i2, i3, e, i4, e, i5, i6, e7]
         * output will be [e, i1, i3, e, i4, e, i5, i7]
         */
        val result = ArrayList<StackTraceElement>(size - probeIndex + 1)
        result += artificialFrame(ARTIFICIAL_FRAME_MESSAGE)
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
