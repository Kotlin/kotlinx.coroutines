/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debugging

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.*

public class DebugCoroutineInfo internal constructor(
    private val delegate: DebugCoroutineInfoImpl,
    public val context: CoroutineContext
) { 
    /**
     * [Job] associated with a current coroutine or null.
     */
    public val job: Job? get() = context[Job]

    /**
     * Last observed state of the coroutine
     * // TODO: should pass enum value
     */
    @JvmField
    public val state: String = delegate.state
    
    /**
     * Last active thread used by a coroutine captured on its suspension or resumption point.
     */
    @JvmField
    public val lastObservedThread: Thread? = delegate.lastObservedThread

    /**
     * Last observed coroutine frame captured on its suspension or resumption point.
     */
    @JvmField
    public val lastObservedFrame: CoroutineStackFrame? = delegate.lastObservedFrame

    /**
     * Creation stacktrace of the coroutine.
     */
    public val creationStackTrace: List<StackTraceElement> = delegate.creationStackTrace

    /**
     * TODO: Note, this implementation is copied from kotlinx.coroutines.debug.internal.DebugProbesImpl
     */
    public fun enhanceStackTraceWithThreadDumpAsJson(): String {
        val stackTraceElements = enhanceStackTraceWithThreadDumpImpl(state, lastObservedThread, delegate.lastObservedStackTrace())
        val stackTraceElementsInfoAsJson = mutableListOf<String>()
        for (element in stackTraceElements) {
            stackTraceElementsInfoAsJson.add(
                """
                {
                    "declaringClass": "${element.className}",
                    "methodName": "${element.methodName}",
                    "fileName": ${element.fileName?.toString()?.repr()},
                    "lineNumber": ${element.lineNumber}
                }
                """.trimIndent()
            )
        }

        return "[${stackTraceElementsInfoAsJson.joinToString()}]"
    }
    

    // TODO: Note, this implementation is copied from kotlinx.coroutines.debug.internal.DebugProbesImpl
    private fun String.repr(): String = buildString {
        append('"')
        for (c in this@repr) {
            when (c) {
                '"' -> append("\\\"")
                '\\' -> append("\\\\")
                '\b' -> append("\\b")
                '\n' -> append("\\n")
                '\r' -> append("\\r")
                '\t' -> append("\\t")
                else -> append(c)
            }
        }
        append('"')
    }

    /**
     * TODO: Note, this implementation is copied from kotlinx.coroutines.debug.internal.DebugProbesImpl
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
         * TODO: Note, this implementation is copied from kotlinx.coroutines.debug.internal.DebugProbesImpl
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
     * TODO: Note, this implementation is copied from kotlinx.coroutines.debug.internal.DebugProbesImpl
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

    // TODO: Note, this implementation is copied from kotlinx.coroutines.debug.internal.DebugProbesImpl
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
}
