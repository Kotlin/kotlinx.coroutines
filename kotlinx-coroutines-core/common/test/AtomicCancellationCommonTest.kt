package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.sync.*
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
    fun testUndispatchedLaunch() = runTest {
        expect(1)
        assertFailsWith<CancellationException> {
            withContext(Job()) {
                cancel()
                launch(start = CoroutineStart.UNDISPATCHED) {
                    expect(2)
                    yield()
                    expectUnreached()
                }
            }
        }
        finish(3)
    }

    @Test
    fun testUndispatchedLaunchWithUnconfinedContext() = runTest {
        expect(1)
        assertFailsWith<CancellationException> {
            withContext(Dispatchers.Unconfined + Job()) {
                cancel()
                launch(start = CoroutineStart.UNDISPATCHED) {
                    expect(2)
                    yield()
                    expectUnreached()
                }
            }
        }
        finish(3)
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
        expect(3) // continues to execute when the job suspends
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
        expect(3) // continues to execute when the job suspends
        yield() // to jobToJoin & canceller
        expect(6)
    }

    @Test
    fun testLockCancellable() = runTest {
        expect(1)
        val mutex = Mutex(true) // locked mutex
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            mutex.lock() // suspends
            expectUnreached() // should NOT execute because of cancellation
        }
        expect(3)
        mutex.unlock() // unlock mutex first
        job.cancel() // cancel the job next
        yield() // now yield
        finish(4)
    }

    @Test
    fun testSelectLockCancellable() = runTest {
        expect(1)
        val mutex = Mutex(true) // locked mutex
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            select<String> { // suspends
                mutex.onLock {
                    expect(4)
                    "OK"
                }
            }
            expectUnreached() // should NOT execute because of cancellation
        }
        expect(3)
        mutex.unlock() // unlock mutex first
        job.cancel() // cancel the job next
        yield() // now yield
        finish(4)
    }
}
