/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.test.*
import java.util.concurrent.ExecutorService
import java.util.concurrent.Executors
import java.util.concurrent.ThreadFactory
import java.util.concurrent.atomic.AtomicInteger
import kotlin.coroutines.CoroutineContext

class WithTimeoutOrNullThreadDispatchTest : TestBase() {
    var executor: ExecutorService? = null

    @AfterTest
    fun tearDown() {
        executor?.shutdown()
    }

    @Test
    fun testCancellationDispatchScheduled() {
        checkCancellationDispatch {
            executor = Executors.newScheduledThreadPool(1, it)
            executor!!.asCoroutineDispatcher()
        }
    }

    @Test
    fun testCancellationDispatchNonScheduled() {
        checkCancellationDispatch {
            executor = Executors.newSingleThreadExecutor(it)
            executor!!.asCoroutineDispatcher()
        }
    }

    @Test
    fun testCancellationDispatchCustomNoDelay() {
        // it also checks that there is at most once scheduled request in flight (no spurious concurrency)
        var error: String? = null
        checkCancellationDispatch {
            executor = Executors.newSingleThreadExecutor(it)
            val scheduled = AtomicInteger(0)
            object : CoroutineDispatcher() {
                override fun dispatch(context: CoroutineContext, block: Runnable) {
                    if (scheduled.incrementAndGet() > 1) error = "Two requests are scheduled concurrently"
                    executor!!.execute {
                        scheduled.decrementAndGet()
                        block.run()
                    }
                }
            }
        }
        error?.let { error(it) }
    }

    private fun checkCancellationDispatch(factory: (ThreadFactory) -> CoroutineDispatcher) = runBlocking {
        expect(1)
        var thread: Thread? = null
        val dispatcher = factory(ThreadFactory { Thread(it).also { thread = it } })
        withContext(dispatcher) {
            expect(2)
            assertEquals(thread, Thread.currentThread())
            val result = withTimeoutOrNull(100) {
                try {
                    expect(3)
                    delay(1000)
                    expectUnreached()
                } catch (e: CancellationException) {
                    expect(4)
                    assertEquals(thread, Thread.currentThread())
                    throw e // rethrow
                }
            }
            assertEquals(thread, Thread.currentThread())
            assertEquals(null, result)
            expect(5)
        }
        finish(6)
    }
}