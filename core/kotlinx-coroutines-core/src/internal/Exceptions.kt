/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import java.util.*
import kotlin.coroutines.*

internal actual fun <E : Throwable> recoverStackTrace(exception: E): E {
    if (!DEBUG || exception is CancellationException) {
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
    if (!DEBUG || exception is CancellationException || continuation !is CoroutineStackFrame) {
        return exception
    }

    val stacktrace = createStackTrace(continuation)
    if (stacktrace.isEmpty()) return exception
    val newException = tryCopyException(exception) ?: return exception
    stacktrace.add(0, artificialFrame("Current coroutine stacktrace"))
    newException.stackTrace = stacktrace.toTypedArray()
    return newException
}

@Suppress("UNCHECKED_CAST")
private fun <E : Throwable> tryCopyException(exception: E): E? {
    /*
     * Try to reflectively find constructor(), constructor(message, cause) or constructor(cause).
     * First thing which comes in mind is why we should do it at all? Exceptions are share between coroutines,
     * so we can't safely modify their stacktraces, thus making copy is our only hope
     */
    var newException: E? = null
    try {
        for (constructor in exception.javaClass.constructors.sortedByDescending { it.parameterTypes.size }) {
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


public fun artificialFrame(message: String) = java.lang.StackTraceElement("\b\b\b($message", "\b", "\b", -1)

@Suppress("ACTUAL_WITHOUT_EXPECT")
actual typealias CoroutineStackFrame = kotlin.coroutines.jvm.internal.CoroutineStackFrame

actual typealias StackTraceElement = java.lang.StackTraceElement
