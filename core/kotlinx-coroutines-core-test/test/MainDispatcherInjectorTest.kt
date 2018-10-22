/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.test

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class MainDispatcherInjectorTest : TestBase() {

    @Before
    fun setUp() {
        MainDispatcherInjector.reset()
    }

    @Test
    fun testInjection() = runTest {
        val mainThread = Thread.currentThread()
        newSingleThreadContext("testInjection").use { threadPool ->
            withContext(Dispatchers.Main) {
                assertSame(mainThread, Thread.currentThread())
            }

            MainDispatcherInjector.inject(threadPool)
            withContext(Dispatchers.Main) {
                assertNotSame(mainThread, Thread.currentThread())
            }
            assertSame(mainThread, Thread.currentThread())

            withContext(Dispatchers.Main.immediate) {
                assertNotSame(mainThread, Thread.currentThread())
            }
            assertSame(mainThread, Thread.currentThread())

            MainDispatcherInjector.inject(Dispatchers.Unconfined)
            withContext(Dispatchers.Main.immediate) {
                assertSame(mainThread, Thread.currentThread())
            }
            assertSame(mainThread, Thread.currentThread())
        }
    }

    @Test
    fun testImmediateDispatcher() = runTest {
        MainDispatcherInjector.inject(ImmediateDispatcher())
        expect(1)
        withContext(Dispatchers.Main) {
            expect(3)
        }

        MainDispatcherInjector.inject(RegularDispatcher())
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
