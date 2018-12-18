/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("PropertyName")

package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.sanitize
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.*

/**
 * Class describing coroutine state.
 */
@ExperimentalCoroutinesApi
public data class CoroutineState internal constructor(
    public val continuation: Continuation<*>,
    private val creationStackBottom: CoroutineStackFrame,
    @JvmField internal val sequenceNumber: Long
) {

    /**
     * [Job] associated with a current coroutine or null.
     * May be later used in [DebugProbes.printJob].
     */
    public val jobOrNull: Job? get() = continuation.context[Job]

    /**
     * Creation stacktrace of the coroutine.
     */
    public val creationStackTrace: List<StackTraceElement> get() = creationStackTrace()

    /**
     * Last observed [state][State] of the coroutine.
     */
    public val state: State get() = _state

    private var _state: State = State.CREATED

    private var lastObservedFrame: CoroutineStackFrame? = null

    // Copy constructor
    internal constructor(coroutine: Continuation<*>, state: CoroutineState) : this(
        coroutine,
        state.creationStackBottom,
        state.sequenceNumber
    ) {
        _state = state.state
        this.lastObservedFrame = state.lastObservedFrame
    }

    private fun creationStackTrace(): List<StackTraceElement> {
        // Skip "Coroutine creation stacktrace" frame
        return sequence<StackTraceElement> { yieldFrames(creationStackBottom.callerFrame) }.toList()
    }

    private tailrec suspend fun SequenceScope<StackTraceElement>.yieldFrames(frame: CoroutineStackFrame?) {
        if (frame == null) return
        frame.getStackTraceElement()?.let { yield(it) }
        val caller = frame.callerFrame
        if (caller != null) {
            yieldFrames(caller)
        }
    }

    internal fun updateState(state: State, frame: Continuation<*>) {
        if (_state == state && lastObservedFrame != null) return
        _state = state
        lastObservedFrame = frame as? CoroutineStackFrame
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
            frame.getStackTraceElement()?.let { result.add(sanitize(it)) }
            frame = frame.callerFrame
        }

        return result
    }
}

/**
 * Current state of the coroutine.
 */
public enum class State {
    /**
     * Created, but not yet started.
     */
    CREATED,
    /**
     * Started and running.
     */
    RUNNING,
    /**
     * Suspended.
     */
    SUSPENDED
}
