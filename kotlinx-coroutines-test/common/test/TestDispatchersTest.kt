/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.test.internal.*
import kotlin.coroutines.*
import kotlin.test.*

@NoNative
class TestDispatchersTest: OrderedExecutionTestBase() {

    @BeforeTest
    fun setUp() {
        Dispatchers.setMain(StandardTestDispatcher())
    }

    @AfterTest
    fun tearDown() {
        Dispatchers.resetMain()
    }

    /** Tests that replacing the dispatcher also replaces the default delay implementation. */
    @Test
    @NoJs // AfterTest is asynchronous
    fun testDefaultDelayReplacement() = runTest {
        assertRunsFast {
            delay(10_000)
            withContext(Dispatchers.Default) {
                delay(10_000)
            }
            delay(10_000)
        }
    }

    /**
     * Tests that the dispatch timeout is not affected by the change to the delay implementation.
     *
     * In this case, it checks that there are no spurious notifications about dispatches.
     */
    @Test
    fun testRunTestWithMainAndSmallTimeout() = testResultMap({ fn ->
        assertFailsWith<UncompletedCoroutinesError> { fn() }
    }) {
        runTest(dispatchTimeoutMs = 100) {
            withContext(Dispatchers.Default) {
                suspendCancellableCoroutine<Unit> {
                    nonMockedDelay.scheduleResumeAfterDelay(5_000, it)
                }
            }
            fail("shouldn't be reached")
        }
    }

    /**
     * Tests that the dispatch timeout is not affected by the change to the delay implementation.
     *
     * In this case, it checks that the timeout does not happen immediately.
     */
    @Test
    fun testRunTestWithMainAndLangeTimeout() = runTest(dispatchTimeoutMs = 1_000) {
        withContext(Dispatchers.Default) {
            suspendCancellableCoroutine<Unit> {
                nonMockedDelay.scheduleResumeAfterDelay(50, it)
            }
        }
    }

    /** Tests that asynchronous execution of tests does not happen concurrently with [AfterTest]. */
    @Test
    @NoJs
    fun testMainMocking() = runTest {
        val mainAtStart = TestMainDispatcher.currentTestDispatcher
        assertNotNull(mainAtStart)
        withContext(Dispatchers.Main) {
            delay(10)
        }
        withContext(Dispatchers.Default) {
            delay(10)
        }
        withContext(Dispatchers.Main) {
            delay(10)
        }
        assertSame(mainAtStart, TestMainDispatcher.currentTestDispatcher)
    }

    /** Tests that the mocked [Dispatchers.Main] correctly forwards [Delay] methods. */
    @Test
    fun testMockedMainImplementsDelay() = runTest {
        val main = Dispatchers.Main
        withContext(main) {
            delay(10)
        }
        withContext(Dispatchers.Default) {
            delay(10)
        }
        withContext(main) {
            delay(10)
        }
    }

    /** Tests that [Distpachers.setMain] fails when called with [Dispatchers.Main]. */
    @Test
    fun testSelfSet() {
        assertFailsWith<IllegalArgumentException> { Dispatchers.setMain(Dispatchers.Main) }
    }

    @Test
    fun testImmediateDispatcher() = runTest {
        Dispatchers.setMain(ImmediateDispatcher())
        expect(1)
        withContext(Dispatchers.Main) {
            expect(3)
        }

        Dispatchers.setMain(RegularDispatcher())
        withContext(Dispatchers.Main) {
            expect(6)
        }

        finish(7)
    }

    private inner class ImmediateDispatcher : CoroutineDispatcher() {
        override fun isDispatchNeeded(context: CoroutineContext): Boolean {
            expect(2)
            return false
        }

        override fun dispatch(context: CoroutineContext, block: Runnable) = throw RuntimeException("Shouldn't be reached")
    }

    private inner class RegularDispatcher : CoroutineDispatcher() {
        override fun isDispatchNeeded(context: CoroutineContext): Boolean {
            expect(4)
            return true
        }

        override fun dispatch(context: CoroutineContext, block: Runnable) {
            expect(5)
            block.run()
        }
    }
}
