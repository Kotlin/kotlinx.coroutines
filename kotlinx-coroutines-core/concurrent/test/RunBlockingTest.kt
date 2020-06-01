/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines

import kotlinx.coroutines.exceptions.*
import kotlin.coroutines.*
import kotlin.test.*

class RunBlockingTest : TestBase() {

    @Test
    @Ignore
    fun testWithTimeoutBusyWait() = runMtTest {
        val value = withTimeoutOrNull(10) {
            while (isActive) {
                // Busy wait
            }
            "value"
        }

        assertEquals("value", value)
    }

    @Test
    fun testOtherDispatcher() = runMtTest {
        expect(1)
        val name = "RunBlockingTest.testOtherDispatcher"
        val thread = newSingleThreadContext(name)
        runBlocking(thread) {
            expect(2)
            assertSame(coroutineContext[ContinuationInterceptor], thread)
            assertTrue(currentThreadName().contains(name))
            yield() // should work
            expect(3)
        }
        finish(4)
        thread.close()
    }

    @Test
    fun testCancelWithDelay() {
        // see https://github.com/Kotlin/kotlinx.coroutines/issues/586
        try {
            runBlocking {
                expect(1)
                coroutineContext.cancel()
                expect(2)
                try {
                    delay(1)
                    expectUnreached()
                } finally {
                    expect(3)
                }
            }
            expectUnreached()
        } catch (e: CancellationException) {
            finish(4)
        }
    }

    @Test
    fun testDispatchOnShutdown(): Unit = assertFailsWith<CancellationException> {
        runBlocking {
            expect(1)
            val job = launch(NonCancellable) {
                try {
                    expect(2)
                    delay(Long.MAX_VALUE)
                } finally {
                    finish(4)
                }
            }

            yield()
            expect(3)
            coroutineContext.cancel()
            job.cancel()
        }
    }.let { }

    @Test
    fun testDispatchOnShutdown2(): Unit = assertFailsWith<CancellationException> {
        runBlocking {
            coroutineContext.cancel()
            expect(1)
            val job = launch(NonCancellable, start = CoroutineStart.UNDISPATCHED) {
                try {
                    expect(2)
                    delay(Long.MAX_VALUE)
                } finally {
                    finish(4)
                }
            }

            expect(3)
            job.cancel()
        }
    }.let { }

    @Test
    fun testNestedRunBlocking() = runBlocking {
        delay(100)
        val value = runBlocking {
            delay(100)
            runBlocking {
                delay(100)
                1
            }
        }

        assertEquals(1, value)
    }

    @Test
    fun testIncompleteState() {
        val handle = runBlocking {
            // See #835
            coroutineContext[Job]!!.invokeOnCompletion { }
        }

        handle.dispose()
    }

    @Test
    fun testCancelledParent() {
        val job = Job()
        job.cancel()
        assertFailsWith<CancellationException> {
            runBlocking(job) {
                expectUnreached()
            }
        }
    }
}
