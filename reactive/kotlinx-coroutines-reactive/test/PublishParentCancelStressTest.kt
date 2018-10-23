/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import org.reactivestreams.*
import java.util.concurrent.*
import kotlin.test.*

public class PublishParentCancelStressTest : TestBase() {
    private val dispatcher = newFixedThreadPoolContext(3, "PublishParentCancelStressTest")
    private val N_TIMES = 5000 * stressTestMultiplier

    @After
    fun tearDown() {
        dispatcher.close()
    }

    @Test
    fun testStress() = runTest {
        var unhandled: Throwable? = null
        val handler = CoroutineExceptionHandler { _, ex -> unhandled = ex }
        repeat(N_TIMES) {
            val barrier = CyclicBarrier(4)
            // launch parent job for publisher
            val parent = GlobalScope.async<Unit>(dispatcher + handler) {
                val publisher = publish<Unit> {
                    // BARRIER #1 - child publisher crashes
                    barrier.await()
                    throw TestException()
                }
                var sub: Subscription? = null
                publisher.subscribe(object : Subscriber<Unit> {
                    override fun onComplete() { error("Cannot be reached") }
                    override fun onSubscribe(s: Subscription?) { sub = s }
                    override fun onNext(t: Unit?) { error("Cannot be reached" ) }
                    override fun onError(t: Throwable?) {
                        assertTrue(t is TestException)
                    }
                })
                launch {
                    // BARRIER #3 -- cancel subscription
                    barrier.await()
                    sub!!.cancel()
                }
                // BARRIER #2 -- parent completes
                barrier.await()
                Unit
            }
            // BARRIE #4 - go 1-3 together
            barrier.await()
            // Make sure exception is not lost, but incorporated into parent
            val result = kotlin.runCatching { parent.await() }
            assertTrue(result.exceptionOrNull() is TestException)
            // Make sure unhandled exception handler was not invoked
            assertNull(unhandled)
        }
    }

    private class TestException : Exception()
}