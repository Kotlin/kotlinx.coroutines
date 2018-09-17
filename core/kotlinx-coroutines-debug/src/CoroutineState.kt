/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * Class describing coroutine state.
 */
public class CoroutineState(public val coroutine: Continuation<*>, public val creationStackTrace: List<StackTraceElement>) {

    internal constructor(coroutine: Continuation<*>, creationStackTrace: List<StackTraceElement>,
                         state: State, lastObservedFrame: Continuation<*>?): this(coroutine, creationStackTrace) {
        _state = state
        this.lastObservedFrame = lastObservedFrame
    }

    internal var _state: State = State.CREATED

    /**
     * Last observer state of the coroutine.
     */
    public val state: State get() = _state

    internal var lastObservedFrame: Continuation<*>? = null

    /**
     * Last observed (suspension-point) stacktrace of the coroutine observed on its
     * suspension or resumption point.
     * It means that for [running][State.RUNNING] coroutines resulting stacktrace is inaccurate and
     * reflects stacktrace of the resumption point, not the current stacktrace
     */
    public fun suspensionStackTrace(): List<StackTraceElement> {
        var frame: CoroutineStackFrame? = lastObservedFrame as? CoroutineStackFrame ?: return emptyList()
        val result = ArrayList<StackTraceElement>()
        while (frame != null) {
            frame.getStackTraceElement()?.let { result.add(it) }
            frame = frame.callerFrame
        }

        return result
    }
}

/**
 * Current state of the coroutine.
 */
public enum class State {
    CREATED,
    RUNNING,
    SUSPENDED
}
