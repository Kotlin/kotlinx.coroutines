/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

/* This package name is like this so that
1) the artificial stack frames look pretty, and
2) the IDE reliably navigates to this file. */
package _COROUTINE

/**
 * A collection of artificial stack trace elements to be included in stack traces by the coroutines machinery.
 *
 * There are typically two ways in which one can encounter an artificial stack frame:
 * 1. By using the debug mode, via the stacktrace recovery mechanism; see
 * [stacktrace recovery](https://github.com/Kotlin/kotlinx.coroutines/blob/master/docs/topics/debugging.md#stacktrace-recovery)
 * documentation. The usual way to enable the debug mode is with the [kotlinx.coroutines.DEBUG_PROPERTY_NAME] system
 * property.
 * 2. By looking at the output of DebugProbes; see the
 * [kotlinx-coroutines-debug](https://github.com/Kotlin/kotlinx.coroutines/tree/master/kotlinx-coroutines-debug) module.
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
    fun coroutineCreation(): StackTraceElement = Exception().artificialFrame(_CREATION::class.java.simpleName)

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
    fun coroutineBoundary(): StackTraceElement = Exception().artificialFrame(_BOUNDARY::class.java.simpleName)
}

// These are needed for the IDE navigation to detect that this file does contain the definition.
private class _CREATION
private class _BOUNDARY

internal val ARTIFICIAL_FRAME_PACKAGE_NAME = "_COROUTINE"

/**
 * Forms an artificial stack frame with the given class name.
 *
 * It consists of the following parts:
 * 1. The package name, it seems, is needed for the IDE to detect stack trace elements reliably. It is `_COROUTINE` since
 * this is a valid identifier.
 * 2. Class names represents what type of artificial frame this is.
 * 3. The method name is `_`. The methods not being present in class definitions does not seem to affect navigation.
 */
private fun Throwable.artificialFrame(name: String): StackTraceElement =
    with(stackTrace[0]) { StackTraceElement(ARTIFICIAL_FRAME_PACKAGE_NAME + "." + name, "_", fileName, lineNumber) }
