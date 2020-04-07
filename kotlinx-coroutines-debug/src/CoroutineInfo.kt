/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("PropertyName")

package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.*

/**
 * Class describing coroutine info such as its context, state and stacktrace.
 */
@ExperimentalCoroutinesApi
public class CoroutineInfo internal constructor(
    public val context: CoroutineContext,
    private val creationStackBottom: CoroutineStackFrame?,
    @JvmField internal val sequenceNumber: Long
) {

    /**
     * [Job] associated with a current coroutine or null.
     * May be later used in [DebugProbes.printJob].
     */
    public val job: Job? get() = context[Job]

    /**
     * Creation stacktrace of the coroutine.
     * Can be empty if [DebugProbes.enableCreationStackTraces] is not set.
     */
    public val creationStackTrace: List<StackTraceElement> get() = creationStackTrace()

    /**
     * Last observed [state][State] of the coroutine.
     */
    public val state: State get() = _state

    private var _state: State = State.CREATED

    @JvmField
    internal var lastObservedThread: Thread? = null

    @JvmField
    internal var lastObservedFrame: CoroutineStackFrame? = null

    public fun copy(): CoroutineInfo = CoroutineInfo(context, creationStackBottom, sequenceNumber).also {
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

    internal fun updateState(state: State, frame: Continuation<*>) {
        // Propagate only duplicating transitions to running for KT-29997
        if (_state == state && state == State.SUSPENDED && lastObservedFrame != null) return
        _state = state
        lastObservedFrame = frame as? CoroutineStackFrame
        if (state == State.RUNNING) {
            lastObservedThread = Thread.currentThread()
        } else {
            lastObservedThread = null
        }
    }

    override fun toString(): String = "CoroutineInfo(state=$state,context=$context)"
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
