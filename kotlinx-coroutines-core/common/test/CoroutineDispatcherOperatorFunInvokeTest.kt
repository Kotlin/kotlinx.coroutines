/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.ContinuationInterceptor
import kotlin.coroutines.CoroutineContext
import kotlin.test.*

class CoroutineDispatcherOperatorFunInvokeTest : TestBase() {

    /**
     * Copy pasted from [WithContextTest.testThrowException],
     * then edited to use operator.
     */
    @Test
    fun testThrowException() = runTest {
        expect(1)
        try {
            (wrappedCurrentDispatcher()) {
                expect(2)
                throw AssertionError()
            }
        } catch (e: AssertionError) {
            expect(3)
        }

        yield()
        finish(4)
    }

    /**
     * Copy pasted from [WithContextTest.testWithContextChildWaitSameContext],
     * then edited to use operator fun invoke for [CoroutineDispatcher].
     */
    @Test
    fun testWithContextChildWaitSameContext() = runTest {
        expect(1)
        (wrappedCurrentDispatcher()) {
            expect(2)
            launch {
                // ^^^ schedules to main thread
                expect(4) // waits before return
            }
            expect(3)
            "OK".wrap()
        }.unwrap()
        finish(5)
    }

    private class Wrapper(val value: String) : Incomplete {
        override val isActive: Boolean
            get() = error("")
        override val list: NodeList?
            get() = error("")
    }

    private fun String.wrap() = Wrapper(this)
    private fun Wrapper.unwrap() = value

    private fun CoroutineScope.wrappedCurrentDispatcher() = object : CoroutineDispatcher() {
        val dispatcher = coroutineContext[ContinuationInterceptor] as CoroutineDispatcher
        override fun dispatch(context: CoroutineContext, block: Runnable) {
            dispatcher.dispatch(context, block)
        }

        override fun isDispatchNeeded(context: CoroutineContext): Boolean {
            return dispatcher.isDispatchNeeded(context)
        }

        @InternalCoroutinesApi
        override fun dispatchYield(context: CoroutineContext, block: Runnable) {
            dispatcher.dispatchYield(context, block)
        }
    }
}
