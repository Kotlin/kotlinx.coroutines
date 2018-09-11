/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*
import kotlin.test.*

class RunBlockingTest : TestBase() {

    @Test
    fun testWithTimeoutBusyWait() = runBlocking {
        val value = withTimeoutOrNull(10) {
            while (isActive) {
                // Busy wait
            }
            "value"
        }

        assertEquals("value", value)
    }

    @Test
    fun testPrivateEventLoop() {
        expect(1)
        runBlocking {
            expect(2)
            assertTrue(coroutineContext[ContinuationInterceptor] is EventLoop)
            yield() // is supported!
            expect(3)
        }
        finish(4)
    }

    @Test
    fun testOuterEventLoop() {
        expect(1)
        runBlocking {
            expect(2)
            val outerEventLoop = coroutineContext[ContinuationInterceptor] as EventLoop
            runBlocking(coroutineContext) {
                expect(3)
                // still same event loop
                assertTrue(coroutineContext[ContinuationInterceptor] === outerEventLoop)
                yield() // still works
                expect(4)
            }
            expect(5)
        }
        finish(6)
    }

    @Test
    fun testOtherDispatcher() {
        expect(1)
        val name = "RunBlockingTest.testOtherDispatcher"
        val thread = newSingleThreadContext(name)
        runBlocking(thread) {
            expect(2)
            assertTrue(coroutineContext[ContinuationInterceptor] === thread)
            assertTrue(Thread.currentThread().name.contains(name))
            yield() // should work
            expect(3)
        }
        finish(4)
        thread.close()
    }


    @Test
    fun testCancellation() = newFixedThreadPoolContext(2, "testCancellation").use {
        val job = GlobalScope.launch(it) {
            runBlocking(coroutineContext) {
                while (true) {
                    yield()
                }
            }
        }

        runBlocking {
            job.cancelAndJoin()
        }
    }
}