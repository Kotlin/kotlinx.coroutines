/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import java.util.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

internal actual fun <E : Throwable> recoverStackTrace(exception: E): E {
    if (recoveryDisabled(exception)) return exception
    // No unwrapping on continuation-less path: exception is not reported multiple times via slow paths
    val copy = tryCopyException(exception) ?: return exception
    return copy.sanitizeStackTrace()
}

private fun <E : Throwable> E.sanitizeStackTrace(): E {
    val stackTrace = stackTrace
    val size = stackTrace.size

    val lastIntrinsic = stackTrace.frameIndex("kotlinx.coroutines.internal.StackTraceRecoveryKt")
    val startIndex = lastIntrinsic + 1
    val endIndex = stackTrace.frameIndex("kotlin.coroutines.jvm.internal.BaseContinuationImpl")
    val adjustment = if (endIndex == -1) 0 else size - endIndex
    val trace = Array(size - lastIntrinsic - adjustment) {
        if (it == 0) {
            artificialFrame("Coroutine boundary")
        } else {
            stackTrace[startIndex + it - 1]
        }
    }

    setStackTrace(trace)
    return this
}

internal actual fun <E : Throwable> recoverStackTrace(exception: E, continuation: Continuation<*>): E {
    if (recoveryDisabled(exception) || continuation !is CoroutineStackFrame) return exception
    return recoverFromStackFrame(exception, continuation)
}

private fun <E : Throwable> recoverFromStackFrame(exception: E, continuation: CoroutineStackFrame): E {
    /*
    * Here we are checking whether exception has already recovered stacktrace.
    * If so, we extract initial and merge recovered stacktrace and current one
    */
    val (cause, recoveredStacktrace) = exception.causeAndStacktrace()

    // Try to create an exception of the same type and get stacktrace from continuation
    val newException = tryCopyException(cause) ?: return exception
    val stacktrace = createStackTrace(continuation)
    if (stacktrace.isEmpty()) return exception

    // Merge if necessary
    if (cause !== exception) {
        mergeRecoveredTraces(recoveredStacktrace, stacktrace)
    }

    // Take recovered stacktrace, merge it with existing one if necessary and return
    return createFinalException(cause, newException, stacktrace)
}

/*
 * Here we partially copy original exception stackTrace to make current one much prettier.
 * E.g. for
 * ```
 * fun foo() = async { error(...) }
 * suspend fun bar() = foo().await()
 * ```
 * we would like to produce following exception:
 * IllegalStateException
 *   at foo
 *   at kotlin.coroutines.resumeWith
 *   (Coroutine boundary)
 *   at bar
 *   ...real stackTrace...
 * caused by "IllegalStateException" (original one)
 */
private fun <E : Throwable> createFinalException(cause: E, result: E, resultStackTrace: ArrayDeque<StackTraceElement>): E {
    resultStackTrace.addFirst(artificialFrame("Coroutine boundary"))
    val causeTrace = cause.stackTrace
    val size = causeTrace.frameIndex("kotlin.coroutines.jvm.internal.BaseContinuationImpl")
    if (size == -1) {
        result.stackTrace = resultStackTrace.toTypedArray()
        return result
    }

    val mergedStackTrace = arrayOfNulls<StackTraceElement>(resultStackTrace.size + size)
    for (i in 0 until size) {
        mergedStackTrace[i] = causeTrace[i]
    }

    for ((index, element) in resultStackTrace.withIndex()) {
        mergedStackTrace[size + index] = element
    }

    result.stackTrace = mergedStackTrace
    return result
}

/**
 * Find initial cause of the exception without restored stacktrace.
 * Returns intermediate stacktrace as well in order to avoid excess cloning of array as an optimization.
 */
private fun <E : Throwable> E.causeAndStacktrace(): Pair<E, Array<StackTraceElement>> {
    val cause = cause
    return if (cause != null && cause.javaClass == javaClass) {
        val currentTrace = stackTrace
        if (currentTrace.any { it.isArtificial() })
            cause as E to currentTrace
        else this to emptyArray()
    } else {
        this to emptyArray()
    }
}

private fun mergeRecoveredTraces(recoveredStacktrace: Array<StackTraceElement>, result: ArrayDeque<StackTraceElement>) {
    // Merge two stacktraces and trim common prefix
    val startIndex = recoveredStacktrace.indexOfFirst { it.isArtificial() } + 1
    val lastFrameIndex = recoveredStacktrace.size - 1
    for (i in lastFrameIndex downTo startIndex) {
        val element = recoveredStacktrace[i]
        if (element.elementWiseEquals(result.last)) {
            result.removeLast()
        }
        result.addFirst(recoveredStacktrace[i])
    }
}

@Suppress("NOTHING_TO_INLINE")
internal actual suspend inline fun recoverAndThrow(exception: Throwable): Nothing {
    if (recoveryDisabled(exception)) throw exception
    suspendCoroutineUninterceptedOrReturn<Nothing> {
        if (it !is CoroutineStackFrame) throw exception
        throw recoverFromStackFrame(exception, it)
    }
}

internal actual fun <E : Throwable> unwrap(exception: E): E {
    if (recoveryDisabled(exception)) return exception
    val cause = exception.cause
    // Fast-path to avoid array cloning
    if (cause == null || cause.javaClass != exception.javaClass) {
        return exception
    }
    // Slow path looks for artificial frames in a stack-trace
    if (exception.stackTrace.any { it.isArtificial() }) {
        @Suppress("UNCHECKED_CAST")
        return cause as E
    } else {
        return exception
    }
}

private fun <E : Throwable> recoveryDisabled(exception: E) =
    !RECOVER_STACK_TRACES || exception is NonRecoverableThrowable

private fun createStackTrace(continuation: CoroutineStackFrame): ArrayDeque<StackTraceElement> {
    val stack = ArrayDeque<StackTraceElement>()
    continuation.getStackTraceElement()?.let { stack.add(it) }

    var last = continuation
    while (true) {
        last = (last as? CoroutineStackFrame)?.callerFrame ?: break
        last.getStackTraceElement()?.let { stack.add(it) }
    }
    return stack
}

/**
 * @suppress
 */
@InternalCoroutinesApi
public fun artificialFrame(message: String) = java.lang.StackTraceElement("\b\b\b($message", "\b", "\b", -1)
internal fun StackTraceElement.isArtificial() = className.startsWith("\b\b\b")
private fun Array<StackTraceElement>.frameIndex(methodName: String) = indexOfFirst { methodName == it.className }

private fun StackTraceElement.elementWiseEquals(e: StackTraceElement): Boolean {
    /*
     * In order to work on Java 9 where modules and classloaders of enclosing class
     * are part of the comparison
     */
    return lineNumber == e.lineNumber && methodName == e.methodName
            && fileName == e.fileName && className == e.className
}

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias CoroutineStackFrame = kotlin.coroutines.jvm.internal.CoroutineStackFrame

@Suppress("ACTUAL_WITHOUT_EXPECT")
internal actual typealias StackTraceElement = java.lang.StackTraceElement
