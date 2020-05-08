/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.internal

import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.*

internal const val CREATED = "CREATED"
internal const val RUNNING = "RUNNING"
internal const val SUSPENDED = "SUSPENDED"

internal class DebugCoroutineInfo(
    public val context: CoroutineContext,
    public val creationStackBottom: CoroutineStackFrame?,
    @JvmField internal val sequenceNumber: Long
) {

    public val creationStackTrace: List<StackTraceElement> get() = creationStackTrace()

    /**
     * Last observed state of the coroutine.
     * Can be CREATED, RUNNING, SUSPENDED.
     */
    public val state: String get() = _state
    private var _state: String = CREATED

    @JvmField
    internal var lastObservedThread: Thread? = null
    @JvmField
    internal var lastObservedFrame: CoroutineStackFrame? = null

    public fun copy(): DebugCoroutineInfo = DebugCoroutineInfo(
        context,
        creationStackBottom,
        sequenceNumber
    ).also {
        it._state = _state
        it.lastObservedFrame = lastObservedFrame
        it.lastObservedThread = lastObservedThread
    }

    /**
     * Last observed stacktrace of the coroutine captured on its suspension or resumption point.
     * It means that for [running][State.RUNNING] coroutines resulting stacktrace is inaccurate and
     * reflects stacktrace of the resumption point, not the actual current stacktrace.
     */
    public fun lastObservedStackTrace(): List<StackTraceElement> {
        var frame: CoroutineStackFrame? = lastObservedFrame ?: return emptyList()
        val result = ArrayList<StackTraceElement>()
        while (frame != null) {
            frame.getStackTraceElement()?.let { result.add(it) }
            frame = frame.callerFrame
        }
        return result
    }

    private fun creationStackTrace(): List<StackTraceElement> {
        val bottom = creationStackBottom ?: return emptyList()
        // Skip "Coroutine creation stacktrace" frame
        return sequence<StackTraceElement> { yieldFrames(bottom.callerFrame) }.toList()
    }

    private tailrec suspend fun SequenceScope<StackTraceElement>.yieldFrames(frame: CoroutineStackFrame?) {
        if (frame == null) return
        frame.getStackTraceElement()?.let { yield(it) }
        val caller = frame.callerFrame
        if (caller != null) {
            yieldFrames(caller)
        }
    }

    internal fun updateState(state: String, frame: Continuation<*>) {
        // Propagate only duplicating transitions to running for KT-29997
        if (_state == state && state == SUSPENDED && lastObservedFrame != null) return
        _state = state
        lastObservedFrame = frame as? CoroutineStackFrame
        lastObservedThread = if (state == RUNNING) {
            Thread.currentThread()
        } else {
            null
        }
    }

    override fun toString(): String = "DebugCoroutineInfo(state=$state,context=$context)"
}
