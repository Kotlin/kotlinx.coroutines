/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * Testable main dispatcher used by kotlinx-coroutines-test.
 * It is a [MainCoroutineDispatcher] which delegates all actions to a settable delegate.
 */
// TODO implement delay
internal class TestMainDispatcher(private val mainFactory: MainDispatcherFactory) : MainCoroutineDispatcher() {

    private var _delegate: CoroutineDispatcher? = null
    private val delegate: CoroutineDispatcher get() {
        if (_delegate != null) return _delegate!!

        val newInstance = createDispatcher()
        if (newInstance != null) {
            _delegate = newInstance
            return newInstance
        }

        // Return missing dispatcher, but do not set _delegate
        return mainFactory.tryCreateDispatcher(emptyList())
    }

    @ExperimentalCoroutinesApi
    override val immediate: MainCoroutineDispatcher
        get() = (delegate as? MainCoroutineDispatcher)?.immediate ?: this

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        delegate.dispatch(context, block)
    }

    @ExperimentalCoroutinesApi
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = delegate.isDispatchNeeded(context)

    public fun setDispatcher(dispatcher: CoroutineDispatcher) {
        _delegate = dispatcher
    }

    public fun resetDispatcher() {
        _delegate = null
    }

    private fun createDispatcher(): CoroutineDispatcher? {
        return try {
            mainFactory.createDispatcher(emptyList())
        } catch (cause: Throwable) {
            null
        }
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
     * [Int.MAX_VALUE] -- test dispatcher always wins no matter what factories are present in classpath.
     * By default all actions are delegated to the second-priority dispatcher, so it won't be the issue.
     */
    override val loadPriority: Int
        get() = Int.MAX_VALUE
}
