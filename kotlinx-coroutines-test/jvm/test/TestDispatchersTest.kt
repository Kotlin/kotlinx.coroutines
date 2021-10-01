/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import kotlin.coroutines.*
import kotlin.test.*

class TestDispatchersTest : TestBase() {

    @BeforeTest
    fun setUp() {
        Dispatchers.resetMain()
    }

    @Test
    fun testSelfSet() = runTest {
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

        override fun dispatch(context: CoroutineContext, block: Runnable) = expectUnreached()
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
