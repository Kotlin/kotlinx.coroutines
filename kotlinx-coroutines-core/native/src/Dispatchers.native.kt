/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.atomicfu.locks.*
import kotlinx.atomicfu.locks.SynchronizedObject
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.internal.multithreadingSupported
import kotlin.coroutines.*

public actual object Dispatchers {
    public actual val Default: CoroutineDispatcher get() = DefaultDispatcher
    public actual val Main: MainCoroutineDispatcher = createMainDispatcher(Default)
    public actual val Unconfined: CoroutineDispatcher get() = kotlinx.coroutines.Unconfined // Avoid freezing

    private var injectedMainDispatcher: MainCoroutineDispatcher? = null

    @PublishedApi
    internal fun injectMain(dispatcher: MainCoroutineDispatcher) {
        if (!multithreadingSupported) {
            throw IllegalStateException("Dispatchers.setMain is not supported in Kotlin/Native when new memory model is disabled")
        }
        injectedMainDispatcher = dispatcher
    }

    @PublishedApi
    internal fun resetInjectedMain() {
        injectedMainDispatcher = null
    }
}

internal expect fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher

// Create DefaultDispatcher thread only when explicitly requested
internal object DefaultDispatcher : CoroutineDispatcher(), Delay, ThreadBoundInterceptor {
    private val lock = SynchronizedObject()
    private val _delegate = atomic<CloseableCoroutineDispatcher?>(null)
//    private val delegate by lazy { newSingleThreadContext("DefaultDispatcher") }
    private val delegate: CloseableCoroutineDispatcher
        get() = _delegate.value ?: getOrCreateDefaultDispatcher()

    private fun getOrCreateDefaultDispatcher() = lock.withLock {
        _delegate.value ?: newSingleThreadContext("DefaultDispatcher").also { _delegate.value = it }
    }

    override val thread: Thread
        get() = delegate.thread
    override fun dispatch(context: CoroutineContext, block: Runnable) =
        delegate.dispatch(context, block)
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) =
        (delegate as Delay).scheduleResumeAfterDelay(timeMillis, continuation)
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        (delegate as Delay).invokeOnTimeout(timeMillis, block, context)
    override fun toString(): String =
        delegate.toString()

    // only for tests
    internal fun shutdown() {
        _delegate.getAndSet(null)?.close()
    }
}
