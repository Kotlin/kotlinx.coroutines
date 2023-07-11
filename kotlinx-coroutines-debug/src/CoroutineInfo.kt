/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE", "UNUSED")
package kotlinx.coroutines.debug

import kotlinx.coroutines.*
import kotlinx.coroutines.debug.internal.*
import kotlin.coroutines.*
import kotlin.coroutines.jvm.internal.*

/**
 * Class describing coroutine info such as its context, state and stacktrace.
 */
@ExperimentalCoroutinesApi
public class CoroutineInfo internal constructor(delegate: DebugCoroutineInfo) {
    /**
     * [Coroutine context][coroutineContext] of the coroutine
     */
    public val context: CoroutineContext = delegate.context

    /**
     * Last observed state of the coroutine
     */
    public val state: State = State.valueOf(delegate.state)

    private val creationStackBottom: CoroutineStackFrame? = delegate.creationStackBottom

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

    private val lastObservedFrame: CoroutineStackFrame? = delegate.lastObservedFrame

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
