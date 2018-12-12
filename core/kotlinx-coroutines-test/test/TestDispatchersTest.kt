/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.test

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import java.lang.IllegalArgumentException
import kotlin.coroutines.*
import kotlin.test.*

class TestDispatchersTest : TestBase() {

    @Before
    fun setUp() {
        Dispatchers.resetMain()
    }

    @Test(expected = IllegalArgumentException::class)
    fun testSelfSet() = runTest {
        Dispatchers.setMain(Dispatchers.Main)
    }

    @Test
    fun testSingleThreadExecutor() = runTest {
        val mainThread = Thread.currentThread()
        Dispatchers.setMain(Dispatchers.Unconfined)
        newSingleThreadContext("testSingleThread").use { threadPool ->
            withContext(Dispatchers.Main) {
                assertSame(mainThread, Thread.currentThread())
            }

            Dispatchers.setMain(threadPool)
            withContext(Dispatchers.Main) {
                assertNotSame(mainThread, Thread.currentThread())
            }
            assertSame(mainThread, Thread.currentThread())

            withContext(Dispatchers.Main.immediate) {
                assertNotSame(mainThread, Thread.currentThread())
            }
            assertSame(mainThread, Thread.currentThread())

            Dispatchers.setMain(Dispatchers.Unconfined)
            withContext(Dispatchers.Main.immediate) {
                assertSame(mainThread, Thread.currentThread())
            }
            assertSame(mainThread, Thread.currentThread())
        }
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
