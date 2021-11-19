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
