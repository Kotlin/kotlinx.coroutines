/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.selects.*
import kotlinx.coroutines.experimental.sync.*
import kotlin.test.*

class AtomicCancellationCommonTest : TestBase() {
    @Test
    fun testCancellableLaunch() = runTest {
        expect(1)
        val job = launch {
            expectUnreached() // will get cancelled before start
        }
        expect(2)
        job.cancel()
        finish(3)
    }

    @Test
    fun testAtomicLaunch() = runTest {
        expect(1)
        val job = launch(start = CoroutineStart.ATOMIC) {
            finish(4) // will execute even after it was cancelled
        }
        expect(2)
        job.cancel()
        expect(3)
    }

    @Test
    fun testDeferredAwaitCancellable() = runTest {
        expect(1)
        val deferred = async { // deferred, not yet complete
            expect(4)
            "OK"
        }
        assertEquals(false, deferred.isCompleted)
        var job: Job? = null
        launch { // will cancel job as soon as deferred completes
            expect(5)
            assertEquals(true, deferred.isCompleted)
            job!!.cancel()
        }
        job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                deferred.await() // suspends
                expectUnreached() // will not execute -- cancelled while dispatched
            } finally {
                finish(7) // but will execute finally blocks
            }
        }
        expect(3) // continues to execute when job suspends
        yield() // to deferred & canceller
        expect(6)
    }

    @Test
    fun testJobJoinCancellable() = runTest {
        expect(1)
        val jobToJoin = launch { // not yet complete
            expect(4)
        }
        assertEquals(false, jobToJoin.isCompleted)
        var job: Job? = null
        launch { // will cancel job as soon as jobToJoin completes
            expect(5)
            assertEquals(true, jobToJoin.isCompleted)
            job!!.cancel()
        }
        job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                jobToJoin.join() // suspends
                expectUnreached() // will not execute -- cancelled while dispatched
            } finally {
                finish(7) // but will execute finally blocks
            }
        }
        expect(3) // continues to execute when job suspends
        yield() // to jobToJoin & canceller
        expect(6)
    }

    @Test
    fun testLockAtomicCancel() = runTest {
        expect(1)
        val mutex = Mutex(true) // locked mutex
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            mutex.lock() // suspends
            expect(4) // should execute despite cancellation
        }
        expect(3)
        mutex.unlock() // unlock mutex first
        job.cancel() // cancel the job next
        yield() // now yield
        finish(5)
    }

    @Test
    fun testSelectLockAtomicCancel() = runTest {
        expect(1)
        val mutex = Mutex(true) // locked mutex
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val result = select<String> { // suspends
                mutex.onLock {
                    expect(4)
                    "OK"
                }
            }
            assertEquals("OK", result)
            expect(5) // should execute despite cancellation
        }
        expect(3)
        mutex.unlock() // unlock mutex first
        job.cancel() // cancel the job next
        yield() // now yield
        finish(6)
    }
}