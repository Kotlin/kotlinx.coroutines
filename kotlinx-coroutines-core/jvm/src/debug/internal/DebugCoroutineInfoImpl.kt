/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug.internal

import java.lang.ref.*
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.*

internal const val CREATED = "CREATED"
internal const val RUNNING = "RUNNING"
internal const val SUSPENDED = "SUSPENDED"

/**
 * Internal implementation class where debugger tracks details it knows about each coroutine.
 */
internal class DebugCoroutineInfoImpl(
    context: CoroutineContext?,
    /**
     * A reference to a stack-trace that is converted to a [StackTraceFrame] which implements [CoroutineStackFrame].
     * The actual reference to the coroutine is not stored here, so we keep a strong reference.
     */
    public val creationStackBottom: StackTraceFrame?,
    @JvmField internal val sequenceNumber: Long
) {
    /**
     * We cannot keep a strong reference to the context, because with the [Job] in the context it will indirectly
     * keep a reference to the last frame of an abandoned coroutine which the debugger should not be preventing
     * garbage-collection of. The reference to context will not disappear as long as the coroutine itself is not lost.
     */
    private val _context = WeakReference(context)
    public val context: CoroutineContext? // can be null when the coroutine was already garbage-collected
        get() = _context.get()

    public val creationStackTrace: List<StackTraceElement> get() = creationStackTrace()

    /**
     * Last observed state of the coroutine.
     * Can be CREATED, RUNNING, SUSPENDED.
     */
    public val state: String get() = _state
    private var _state: String = CREATED

    @JvmField
    internal var lastObservedThread: Thread? = null

    /**
     * We cannot keep a strong reference to the last observed frame of the coroutine, because this will
     * prevent garbage-collection of a coroutine that was lost.
     */
    private var _lastObservedFrame: WeakReference<CoroutineStackFrame>? = null
    internal var lastObservedFrame: CoroutineStackFrame?
        get() = _lastObservedFrame?.get()
        set(value) { _lastObservedFrame = value?.let { WeakReference(it) } }

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
        return sequence { yieldFrames(bottom.callerFrame) }.toList()
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
