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
internal class TestMainDispatcher(var delegate: CoroutineDispatcher):
    MainCoroutineDispatcher(),
    Delay
{
    private val mainDispatcher = delegate // the initial value passed to the constructor

    private val delay
        get() = delegate as? Delay ?: defaultDelay

    override val immediate: MainCoroutineDispatcher
        get() = (delegate as? MainCoroutineDispatcher)?.immediate ?: this

    override fun dispatch(context: CoroutineContext, block: Runnable) = delegate.dispatch(context, block)

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = delegate.isDispatchNeeded(context)

    override fun dispatchYield(context: CoroutineContext, block: Runnable) = delegate.dispatchYield(context, block)

    fun resetDispatcher() {
        delegate = mainDispatcher
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) =
        delay.scheduleResumeAfterDelay(timeMillis, continuation)

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        delay.invokeOnTimeout(timeMillis, block, context)
}

@Suppress("INVISIBLE_MEMBER")
private val defaultDelay
    inline get() = DefaultDelay

@Suppress("INVISIBLE_MEMBER")
internal expect fun Dispatchers.getTestMainDispatcher(): TestMainDispatcher