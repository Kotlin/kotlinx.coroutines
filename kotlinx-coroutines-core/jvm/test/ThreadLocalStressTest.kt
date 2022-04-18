/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.sync.*
import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.test.*


class ThreadLocalStressTest : TestBase() {

    private val threadLocal = ThreadLocal<String>()

    // See the comment in doStress for the machinery
    @Test
    fun testStress() = runTest {
        repeat (100 * stressTestMultiplierSqrt) {
            withContext(Dispatchers.Default) {
                repeat(100) {
                    launch {
                        doStress(null)
                    }
                }
            }
        }
    }

    @Test
    fun testStressWithOuterValue() = runTest {
        repeat (100 * stressTestMultiplierSqrt) {
            withContext(Dispatchers.Default + threadLocal.asContextElement("bar")) {
                repeat(100) {
                    launch {
                        doStress("bar")
                    }
                }
            }
        }
    }

    private suspend fun doStress(expectedValue: String?) {
        assertEquals(expectedValue, threadLocal.get())
        try {
            /*
             * Here we are using very specific code-path to trigger the execution we want to.
             * The bug, in general, has a larger impact, but this particular code pinpoints it:
             *
             * 1) We use _undispatched_ withContext with thread element
             * 2) We cancel the coroutine
             * 3) We use 'suspendCancellableCoroutineReusable' that does _postponed_ cancellation check
             *    which makes the reproduction of this race pretty reliable.
             *
             * Now the following code path is likely to be triggered:
             *
             * T1 from within 'withContinuationContext' method:
             * Finds 'oldValue', finds undispatched completion, invokes its 'block' argument.
             * 'block' is this coroutine, it goes to 'trySuspend', checks for postponed cancellation and *dispatches* it.
             * The execution stops _right_ before 'undispatchedCompletion.clearThreadContext()'.
             *
             * T2 now executes the dispatched cancellation and concurrently mutates the state of the undispatched completion.
             * All bets are off, now both threads can leave the thread locals state inconsistent.
             */
            withContext(threadLocal.asContextElement("foo")) {
                yield()
                cancel()
                suspendCancellableCoroutineReusable<Unit> { }
            }
        } finally {
            assertEquals(expectedValue, threadLocal.get())
        }
    }

    /*
     * Another set of tests for undispatcheable continuations that do not require stress test multiplier.
     * Also note that `uncaughtExceptionHandler` is used as the only available mechanism to propagate error from
     * `resumeWith`
     */

    @Test
    fun testNonDispatcheableLeak() {
        repeat(100) {
            doTestWithPreparation(
                ::doTest,
                { threadLocal.set(null) }) { threadLocal.get() == null }
            assertNull(threadLocal.get())
        }
    }

    @Test
    fun testNonDispatcheableLeakWithInitial() {
        repeat(100) {
            doTestWithPreparation(::doTest, { threadLocal.set("initial") }) { threadLocal.get() == "initial" }
            assertEquals("initial", threadLocal.get())
        }
    }

    @Test
    fun testNonDispatcheableLeakWithContextSwitch() {
        repeat(100) {
            doTestWithPreparation(
                ::doTestWithContextSwitch,
                { threadLocal.set(null) }) { threadLocal.get() == null }
            assertNull(threadLocal.get())
        }
    }

    @Test
    fun testNonDispatcheableLeakWithInitialWithContextSwitch() {
        repeat(100) {
            doTestWithPreparation(
                ::doTestWithContextSwitch,
                { threadLocal.set("initial") }) { true /* can randomly wake up on the non-main thread */ }
            // Here we are always on the main thread
            assertEquals("initial", threadLocal.get())
        }
    }

    private fun doTestWithPreparation(testBody: suspend () -> Unit, setup: () -> Unit, isValid: () -> Boolean) {
        setup()
        val latch = CountDownLatch(1)
        testBody.startCoroutineUninterceptedOrReturn(Continuation(EmptyCoroutineContext) {
            if (!isValid()) {
                Thread.currentThread().uncaughtExceptionHandler.uncaughtException(
                    Thread.currentThread(),
                    IllegalStateException("Unexpected error: thread local was not cleaned")
                )
            }
            latch.countDown()
        })
        latch.await()
    }

    private suspend fun doTest() {
        withContext(threadLocal.asContextElement("foo")) {
            try {
                coroutineScope {
                    val semaphore = Semaphore(1, 1)
                    cancel()
                    semaphore.acquire()
                }
            } catch (e: CancellationException) {
                // Ignore cancellation
            }
        }
    }

    private suspend fun doTestWithContextSwitch() {
        withContext(threadLocal.asContextElement("foo")) {
            try {
                coroutineScope {
                    val semaphore = Semaphore(1, 1)
                    GlobalScope.launch { }.join()
                    cancel()
                    semaphore.acquire()
                }
            } catch (e: CancellationException) {
                // Ignore cancellation
            }
        }
    }
}
