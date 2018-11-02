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
    override val defaultResumeMode: Int get() = MODE_DIRECT

    @Suppress("UNCHECKED_CAST")
    internal override fun onCompletionInternal(state: Any?, mode: Int, suppressed: Boolean) {
        if (state is CompletedExceptionally)
            uCont.resumeUninterceptedWithExceptionMode(state.cause, mode)
        else
            uCont.resumeUninterceptedMode(state as T, mode)
    }
}

internal class ContextScope(context: CoroutineContext) : CoroutineScope {
    override val coroutineContext: CoroutineContext = context
}
