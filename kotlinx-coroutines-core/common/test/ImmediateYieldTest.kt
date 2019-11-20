/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.test.*

class ImmediateYieldTest : TestBase() {

    // See https://github.com/Kotlin/kotlinx.coroutines/issues/1474
    @Test
    fun testImmediateYield() = runTest {
        expect(1)
        launch(ImmediateDispatcher(coroutineContext[ContinuationInterceptor])) {
            expect(2)
            yield()
            expect(4)
        }
        expect(3) // after yield
        yield() // yield back
        finish(5)
    }

    // imitate immediate dispatcher
    private class ImmediateDispatcher(job: ContinuationInterceptor?) : CoroutineDispatcher() {
        val delegate: CoroutineDispatcher = job as CoroutineDispatcher

        override fun isDispatchNeeded(context: CoroutineContext): Boolean = false

        override fun dispatch(context: CoroutineContext, block: Runnable) =
            delegate.dispatch(context, block)
    }

    @Test
    fun testWrappedUnconfinedDispatcherYield() = runTest {
        expect(1)
        launch(wrapperDispatcher(Dispatchers.Unconfined)) {
            expect(2)
            yield() // Would not work with wrapped unconfined dispatcher
            expect(3)
        }
        finish(4) // after launch
    }
}