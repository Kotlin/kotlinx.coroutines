/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import java.util.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*

internal actual fun <E : Throwable> recoverStackTrace(exception: E): E {
    if (recoveryDisabled(exception)) {
        return exception
    }

    val copy = tryCopyException(exception) ?: return exception
    return copy.sanitizeStackTrace()
}

private fun <E : Throwable> E.sanitizeStackTrace(): E {
    val size = stackTrace.size

    var lastIntrinsic = -1
    for (i in 0 until size) {
        val name = stackTrace[i].className
        if ("kotlinx.coroutines.internal.ExceptionsKt" == name) {
            lastIntrinsic = i
        }
    }

    val startIndex = lastIntrinsic + 1
    val trace = Array(size - lastIntrinsic) {
        if (it == 0) {
            artificialFrame("Current coroutine stacktrace")
        } else {
            stackTrace[startIndex + it - 1]
        }
    }

    stackTrace = trace
    return this
}

internal actual fun <E : Throwable> recoverStackTrace(exception: E, continuation: Continuation<*>): E {
    if (recoveryDisabled(exception) || continuation !is CoroutineStackFrame) {
        return exception
    }

    return recoverFromStackFrame(exception, continuation)
}

private fun <E : Throwable> recoverFromStackFrame(exception: E, continuation: CoroutineStackFrame): E {
    val newException = tryCopyException(exception) ?: return exception
    val stacktrace = createStackTrace(continuation)
    if (stacktrace.isEmpty()) return exception
    stacktrace.add(0, artificialFrame("Current coroutine stacktrace"))
    newException.stackTrace = stacktrace.toTypedArray()
    return newException
}


@Suppress("NOTHING_TO_INLINE")
internal actual suspend inline fun recoverAndThrow(exception: Throwable): Nothing {
    if (recoveryDisabled(exception)) throw exception
    suspendCoroutineUninterceptedOrReturn<Nothing> {
        if (it !is CoroutineStackFrame) throw exception
        throw  recoverFromStackFrame(exception, it)
    }
}

internal actual fun <E : Throwable> unwrap(exception: E): E {
    if (recoveryDisabled(exception)) {
        return exception
    }

    val element = exception.stackTrace.firstOrNull() ?: return exception
    if (element.isArtificial()) {
        @Suppress("UNCHECKED_CAST")
        return exception.cause as? E ?: exception
    } else {
        return exception
    }
}

private fun <E : Throwable> recoveryDisabled(exception: E) =
    !RECOVER_STACKTRACE || !DEBUG || exception is CancellationException || exception is NonRecoverableThrowable

@Suppress("UNCHECKED_CAST")
private fun <E : Throwable> tryCopyException(exception: E): E? {
    /*
     * Try to reflectively find constructor(), constructor(message, cause) or constructor(cause).
     * Exceptions are shared among coroutines, so we should copy exception before recovering current stacktrace.
     */
    var newException: E? = null
    try {
        val constructors = exception.javaClass.constructors.sortedByDescending { it.parameterTypes.size }
        for (constructor in constructors) {
            val parameters = constructor.parameterTypes
            if (parameters.size == 2 && parameters[0] == String::class.java && parameters[1] == Throwable::class.java) {
                newException = constructor.newInstance(exception.message, exception) as E
            } else if (parameters.size == 1 && parameters[0] == Throwable::class.java) {
                newException = constructor.newInstance(exception) as E
            } else if (parameters.isEmpty()) {
                newException = (constructor.newInstance() as E).also { it.initCause(exception) }
            }

            if (newException != null) {
                break
            }
        }
    } catch (e: Exception) {
        // Do nothing
    }
    return newException
}

private fun createStackTrace(continuation: CoroutineStackFrame): ArrayList<StackTraceElement> {
    val stack = ArrayList<StackTraceElement>()
    continuation.getStackTraceElement()?.let { stack.add(it) }

    var last = continuation
    while (true) {
        last = (last as? CoroutineStackFrame)?.callerFrame ?: break
        last.getStackTraceElement()?.let { stack.add(it) }
    }
    return stack
}


internal fun artificialFrame(message: String) = java.lang.StackTraceElement("\b\b\b($message", "\b", "\b", -1)
internal fun StackTraceElement.isArtificial() = className.startsWith("\b\b\b")

@Suppress("ACTUAL_WITHOUT_EXPECT")
actual typealias CoroutineStackFrame = kotlin.coroutines.jvm.internal.CoroutineStackFrame

actual typealias StackTraceElement = java.lang.StackTraceElement
