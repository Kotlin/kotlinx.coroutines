/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test
import kotlinx.coroutines.*
import kotlin.coroutines.*

@ExperimentalCoroutinesApi
public actual fun Dispatchers.setMain(dispatcher: CoroutineDispatcher) {
    require(dispatcher !is TestMainDispatcher) { "Dispatchers.setMain(Dispatchers.Main) is prohibited, probably Dispatchers.resetMain() should be used instead" }
    getTestMainDispatcher().setDispatcher(dispatcher)
}

@ExperimentalCoroutinesApi
public actual fun Dispatchers.resetMain() {
    getTestMainDispatcher().resetDispatcher()
}

private class TestMainDispatcher(private val mainDispatcher: MainCoroutineDispatcher) : MainCoroutineDispatcher(), Delay {
    private var delegate: CoroutineDispatcher = mainDispatcher

    @Suppress("INVISIBLE_MEMBER")
    private val delay: Delay get() = delegate as? Delay ?: DefaultDelay

    override val immediate: MainCoroutineDispatcher
        get() = (delegate as? MainCoroutineDispatcher)?.immediate ?: this

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        delegate.dispatch(context, block)
    }

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = delegate.isDispatchNeeded(context)

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        delay.scheduleResumeAfterDelay(timeMillis, continuation)
    }

    override suspend fun delay(time: Long) {
        delay.delay(time)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        return delay.invokeOnTimeout(timeMillis, block, context)
    }

    fun setDispatcher(dispatcher: CoroutineDispatcher) {
        delegate = dispatcher
    }

    fun resetDispatcher() {
        delegate = mainDispatcher
    }
}

@Suppress("INVISIBLE_MEMBER")
private fun getTestMainDispatcher(): TestMainDispatcher {
    val mainDispatcher = Dispatchers.Main
    return if (mainDispatcher is TestMainDispatcher) {
        mainDispatcher
    } else {
        val injectedDispatcher = TestMainDispatcher(mainDispatcher)
        Dispatchers.injectMain(injectedDispatcher)
        injectedDispatcher
    }
}