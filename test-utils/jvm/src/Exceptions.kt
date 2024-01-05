/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import java.io.*
import java.util.*
import kotlin.coroutines.*
import kotlin.test.*

inline fun <reified T : Throwable> checkException(exception: Throwable): Boolean {
    assertTrue(exception is T)
    assertTrue(exception.suppressed.isEmpty())
    assertNull(exception.cause)
    return true
}

fun checkCycles(t: Throwable) {
    val sw = StringWriter()
    t.printStackTrace(PrintWriter(sw))
    assertFalse(sw.toString().contains("CIRCULAR REFERENCE"))
}

class CapturingHandler : AbstractCoroutineContextElement(CoroutineExceptionHandler),
    CoroutineExceptionHandler
{
    private var unhandled: ArrayList<Throwable>? = ArrayList()

    override fun handleException(context: CoroutineContext, exception: Throwable) = synchronized<Unit>(this) {
        unhandled!!.add(exception)
    }

    fun getExceptions(): List<Throwable> = synchronized(this) {
        return unhandled!!.also { unhandled = null }
    }

    fun getException(): Throwable = synchronized(this) {
        val size = unhandled!!.size
        assert(size == 1) { "Expected one unhandled exception, but have $size: $unhandled" }
        return unhandled!![0].also { unhandled = null }
    }
}

fun captureExceptionsRun(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> Unit
): Throwable {
    val handler = CapturingHandler()
    runBlocking(context + handler, block = block)
    return handler.getException()
}

fun captureMultipleExceptionsRun(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> Unit
): List<Throwable> {
    val handler = CapturingHandler()
    runBlocking(context + handler, block = block)
    return handler.getExceptions()
}
