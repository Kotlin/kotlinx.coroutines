/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.internal
import kotlinx.coroutines.*
import kotlin.coroutines.*

/**
 * The testable main dispatcher used by kotlinx-coroutines-test.
 * It is a [MainCoroutineDispatcher] that delegates all actions to a settable delegate.
 */
internal class TestMainDispatcher(private var delegate: CoroutineDispatcher):
    MainCoroutineDispatcher(),
    Delay by (delegate as? Delay ?: defaultDelay)
{
    private val mainDispatcher = delegate // the initial value passed to the constructor

    override val immediate: MainCoroutineDispatcher
        get() = (delegate as? MainCoroutineDispatcher)?.immediate ?: this

    override fun dispatch(context: CoroutineContext, block: Runnable) = delegate.dispatch(context, block)

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = delegate.isDispatchNeeded(context)

    override fun dispatchYield(context: CoroutineContext, block: Runnable) = delegate.dispatchYield(context, block)

    fun setDispatcher(dispatcher: CoroutineDispatcher) {
        delegate = dispatcher
    }

    fun resetDispatcher() {
        delegate = mainDispatcher
    }
}

@Suppress("INVISIBLE_MEMBER")
private val defaultDelay
    inline get() = DefaultDelay

@Suppress("INVISIBLE_MEMBER")
internal expect fun Dispatchers.getTestMainDispatcher(): TestMainDispatcher