/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
    uCont: Continuation<T>,
    useInitNativeKludge: Boolean
) : AbstractCoroutine<T>(context, true, true), CoroutineStackFrame {
    @JvmField
    val uCont: Continuation<T> = uCont.asShareable() // unintercepted continuation, shareable
    final override val callerFrame: CoroutineStackFrame? get() = uCont.asLocal() as? CoroutineStackFrame
    final override fun getStackTraceElement(): StackTraceElement? = null

    final override val isScopedCoroutine: Boolean get() = true
    internal val parent: Job? get() = parentHandle?.parent

    init {
        // Kludge for native
        if (useInitNativeKludge && !isReuseSupportedInPlatform()) initParentForNativeUndispatchedCoroutine()
    }

    protected open fun initParentForNativeUndispatchedCoroutine() {
        initParentJob(parentContext[Job])
    }

    override fun afterCompletion(state: Any?) {
        // Resume in a cancellable way by default when resuming from another context
        uCont.shareableInterceptedResumeCancellableWith(recoverResult(state, uCont))
    }

    override fun afterResume(state: Any?) {
        // Resume direct because scope is already in the correct context
        uCont.resumeWith(recoverResult(state, uCont))
    }
}

internal class ContextScope(context: CoroutineContext) : CoroutineScope {
    override val coroutineContext: CoroutineContext = context
    // CoroutineScope is used intentionally for user-friendly representation
    override fun toString(): String = "CoroutineScope(coroutineContext=$coroutineContext)"
}
