/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * The testable main dispatcher used by kotlinx-coroutines-test.
 * It is a [MainCoroutineDispatcher] which delegates all actions to a settable delegate.
 */
internal class TestMainDispatcher(private val mainFactory: MainDispatcherFactory) : MainCoroutineDispatcher(), Delay {
    private var _delegate: CoroutineDispatcher? = null
    private val delegate: CoroutineDispatcher get() {
        _delegate?.let { return it }
        mainFactory.tryCreateDispatcher(emptyList()).let {
            // If we've failed to create a dispatcher, do no set _delegate
            if (!isMissing()) {
                _delegate = it
            }
            return it
        }
    }

    @Suppress("INVISIBLE_MEMBER")
    private val delay: Delay get() = delegate as? Delay ?: DefaultDelay

    override val immediate: MainCoroutineDispatcher
        get() = (delegate as? MainCoroutineDispatcher)?.immediate ?: this

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        delegate.dispatch(context, block)
    }

    @ExperimentalCoroutinesApi
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = delegate.isDispatchNeeded(context)

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        delay.scheduleResumeAfterDelay(timeMillis, continuation)
    }

    override suspend fun delay(time: Long) {
        delay.delay(time)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        return delay.invokeOnTimeout(timeMillis, block)
    }

    public fun setDispatcher(dispatcher: CoroutineDispatcher) {
        _delegate = dispatcher
    }

    public fun resetDispatcher() {
        _delegate = null
    }
}

internal class TestMainDispatcherFactory : MainDispatcherFactory {

    override fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher {
        val originalFactory = allFactories.asSequence()
            .filter { it !== this }
            .maxBy { it.loadPriority } ?: MissingMainCoroutineDispatcherFactory
        return TestMainDispatcher(originalFactory)
    }

    /**
     * [Int.MAX_VALUE] -- test dispatcher always wins no matter what factories are present in the classpath.
     * By default all actions are delegated to the second-priority dispatcher, so that it won't be the issue.
     */
    override val loadPriority: Int
        get() = Int.MAX_VALUE
}
