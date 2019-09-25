/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
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
        val result = if (state is CompletedExceptionally)
            Result.failure(recoverStackTrace(state.cause, uCont))
        else
            Result.success(state as T)
        when (mode) {
            MODE_ATOMIC_DEFAULT -> uCont.intercepted().resumeWith(result)
            MODE_CANCELLABLE -> uCont.intercepted().resumeCancellableWith(result)
            MODE_DIRECT -> uCont.resumeWith(result)
            MODE_UNDISPATCHED -> withCoroutineContext(uCont.context, null) { uCont.resumeWith(result) }
            else -> error("Invalid mode $mode")
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
