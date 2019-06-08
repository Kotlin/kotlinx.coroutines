/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * This is a coroutine instance that is created by [coroutineScope] builder.
 */
internal open class ScopeCoroutine<in T>(
    context: CoroutineContext,
    @JvmField val uCont: Continuation<T> // unintercepted continuation
) : AbstractCoroutine<T>(context, true), CoroutineStackFrame {
    final override val callerFrame: CoroutineStackFrame? get() = uCont as CoroutineStackFrame?
    final override fun getStackTraceElement(): StackTraceElement? = null
    final override val isScopedCoroutine: Boolean get() = true

    override val defaultResumeMode: Int get() = MODE_DIRECT

    internal val parent: Job? get() = parentContext[Job]

    @Suppress("UNCHECKED_CAST")
    override fun afterCompletionInternal(state: Any?, mode: Int) {
        if (state is CompletedExceptionally) {
            val exception = if (mode == MODE_IGNORE) state.cause else recoverStackTrace(state.cause, uCont)
            uCont.resumeUninterceptedWithExceptionMode(exception, mode)
        } else {
            uCont.resumeUninterceptedMode(state as T, mode)
        }
    }
}

internal fun AbstractCoroutine<*>.tryRecover(exception: Throwable): Throwable {
    val cont = (this as? ScopeCoroutine<*>)?.uCont ?: return exception
    return recoverStackTrace(exception, cont)
}

internal class ContextScope(context: CoroutineContext) : CoroutineScope {
    override val coroutineContext: CoroutineContext = context
}
