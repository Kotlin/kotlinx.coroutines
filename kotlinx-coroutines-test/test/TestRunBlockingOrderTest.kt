/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import org.junit.*
import kotlin.concurrent.thread
import kotlin.coroutines.*
import kotlin.test.assertEquals

class TestRunBlockingOrderTest : TestBase() {
    @Test
    fun testLaunchImmediate() = runBlockingTest {
        expect(1)
        launch {
            expect(2)
        }
        finish(3)
    }

    @Test
    fun testYield() = runBlockingTest {
        expect(1)
        launch {
            expect(2)
            yield()
            finish(4)
        }
        expect(3)
    }

    @Test
    fun testLaunchWithDelayCompletes() = runBlockingTest {
        expect(1)
        launch {
            delay(100)
            finish(3)
        }
        expect(2)
    }

    @Test
    fun testLaunchDelayOrdered() = runBlockingTest {
        expect(1)
        launch {
            delay(200) // long delay
            finish(4)
        }
        launch  {
            delay(100) // shorter delay
            expect(3)
        }
        expect(2)
    }

    @Test
    fun testInfiniteDelay() = runBlockingTest {
        expect(1)
        delay(100) // move time forward a bit some that naive time + delay gives an overflow
        launch {
            delay(Long.MAX_VALUE) // infinite delay
            finish(4)
        }
        launch  {
            delay(100) // short delay
            expect(3)
        }
        expect(2)
    }

    @Test
    fun testNewThread_inSuspendCancellableCoroutine() = runBlockingTest {
        expect(1)
        suspendCancellableCoroutine<Unit> { cont ->
            expect(2)
            thread {
                expect(3)
                cont.resume(Unit)
            }
        }
        finish(4)
    }

    @Test(expected = UncompletedCoroutinesError::class)
    fun testWithOddlyCompletingJob_fails() {
        // this test is suspect since it relies upon the exact ordering of code in runBlockingTest
        // however, it needs to ensure the job finishes *after* advanceUntilIdle is called in order
        // to ensure that runBlockingTest errors when presented with threading non-determinism.

        // this test is stable and will always pass unless the implementation changes.

        // If this starts failing because the call to cleanupTestCoroutines changes it will need a similarly
        // implementation driven test.

        class FakeDispatcher(val delegate: TestCoroutineDispatcher):
                CoroutineDispatcher(),
                Delay by delegate,
                DelayController by delegate {
            private var cleanupCallback: (() -> Unit)? = null

            override fun dispatch(context: CoroutineContext, block: Runnable) {
                delegate.dispatch(context, block)
            }

            fun onCleanup(block: () -> Unit) {
                cleanupCallback = block
            }

            override fun cleanupTestCoroutines() {
                delegate.cleanupTestCoroutines()
                cleanupCallback?.invoke()
            }
        }

        val dispatcher = FakeDispatcher(TestCoroutineDispatcher())
        val scope = TestCoroutineScope(dispatcher)
        val resumeAfterTest = CompletableDeferred<Unit>()

        scope.runBlockingTest {
            expect(1)
            dispatcher.onCleanup {
                // after advanceTimeUntilIdle, complete the launched coroutine
                expect(3)
                resumeAfterTest.complete(Unit)
                finish(5)
            }
            expect(2)
            resumeAfterTest.await() // this will resume just before child jobs are checked
            expect(4)
        }
    }

    @Test
    fun testThrows_throws() {
        val expected = IllegalStateException("expected")
        val result = runCatching {
            expect(1)
            runBlockingTest {
                expect(2)
                throw expected
            }
        }
        finish(3)
        assertEquals(expected, result.exceptionOrNull())
    }

    @Test
    fun testSuspendForever_fails() {
        val uncompleted = CompletableDeferred<Unit>()
        val result = runCatching {
            expect(1)
            runBlockingTest {
                expect(2)
                uncompleted.await()
            }
        }
        finish(3)
        assertEquals(true, result.isFailure)
    }

    @Test
    fun testAdvanceUntilIdle_inRunBlocking() = runBlockingTest {
        expect(1)
        assertRunsFast {
            advanceUntilIdle()   // ensure this doesn't block forever
        }
        finish(2)
    }
}
