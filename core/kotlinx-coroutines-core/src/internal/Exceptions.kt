/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.coroutines.experimental.jvm.internal.*

internal actual fun <E : Throwable> recoverStackTrace(exception: E): E {
    if (!DEBUG || exception is CancellationException) {
        return exception
    }

    return tryWrapException(exception) ?: exception
}

internal actual fun <E : Throwable> recoverStackTrace(exception: E, continuation: Continuation<*>): E {
    if (!DEBUG || exception is CancellationException || continuation !is CoroutineImpl) {
        return exception
    }

    val newException = tryWrapException(exception) ?: return exception
    val stacktrace = fillInStackTrace(continuation).toTypedArray()
    if (stacktrace.isEmpty()) return exception
    newException.stackTrace = stacktrace
    return newException
}

@Suppress("UNCHECKED_CAST")
private fun <E : Throwable> tryWrapException(exception: E): E? {
    // TODO multi-release JAR to cache in ClassValueMap
    var newException: E? = null
    try {
        for (constructor in exception.javaClass.constructors.sortedBy { -it.parameterTypes.size }) {
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

private fun fillInStackTrace(continuation: Continuation<*>): ArrayList<StackTraceElement> {
    val stack = ArrayList<StackTraceElement>()

    stack.add(stackTraceElement(continuation))
    var last = continuation
    while (true) {
        last = getCompletion(last) ?: break
        stack.add(stackTraceElement(last))
    }
    return stack
}

// TODO basic stub before 1.3
private fun stackTraceElement(continuation: Continuation<*>): StackTraceElement {
    val name = continuation.javaClass.name
    val index = name.indexOf("$")
    if (index == -1) return StackTraceElement(name, "", null, -1)
    val methodName = name.substring(index + 1)
    return StackTraceElement(name.substring(0, index), methodName.substring(0, methodName.lastIndexOf("$")), null, -1)
}

private fun getCompletion(continuation: Continuation<*>): Continuation<*>? {
    // TODO hack before 1.3
    // TODO we may want to support our own builders such as "withContext"
    if (continuation !is CoroutineImpl) return null
    return try {
        val field = CoroutineImpl::class.java.getDeclaredField("completion")
        field.isAccessible = true
        field.get(continuation) as Continuation<*>?
    } catch (t: Throwable) {
        null
    }
}
