/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.debug
import kotlinx.coroutines.*

/**
 * A collection of artificial stack trace elements to be included in stack traces by the coroutines machinery.
 */
internal class ArtificialStackFrames {
    /**
     * Returns an artificial stack trace element denoting the boundary between coroutine creation and its execution.
     *
     * Appearance of this function in stack traces does not mean that it was called. Instead, it is used as a marker
     * that separates the part of the stack trace with the code executed in a coroutine from the stack trace of the code
     * that launched the coroutine.
     *
     * In earlier versions of kotlinx-coroutines, this was displayed as "(Coroutine creation stacktrace)", which caused
     * problems for tooling that processes stack traces: https://github.com/Kotlin/kotlinx.coroutines/issues/2291
     *
     * Note that presence of this marker in a stack trace implies that coroutine creation stack traces were enabled.
     */
    fun coroutineCreation(): StackTraceElement = Exception().artificialFrame()

    /**
     * Returns an artificial stack trace element denoting a coroutine boundary.
     *
     * Appearance of this function in stack traces does not mean that it was called. Instead, when one coroutine invokes
     * another, this is used as a marker in the stack trace to denote where the execution of one coroutine ends and that
     * of another begins.
     *
     * In earlier versions of kotlinx-coroutines, this was displayed as "(Coroutine boundary)", which caused
     * problems for tooling that processes stack traces: https://github.com/Kotlin/kotlinx.coroutines/issues/2291
     */
    fun coroutineBoundary(): StackTraceElement = Exception().artificialFrame()
}

internal val ARTIFICIAL_FRAME_CLASS_NAME = ArtificialStackFrames::class.java.simpleName

private fun Throwable.artificialFrame(): StackTraceElement =
    with(stackTrace[0]) { StackTraceElement(ARTIFICIAL_FRAME_CLASS_NAME, methodName, fileName, lineNumber) }
