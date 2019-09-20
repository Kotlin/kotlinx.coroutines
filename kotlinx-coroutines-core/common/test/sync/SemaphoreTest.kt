package kotlinx.coroutines.sync

import kotlinx.coroutines.*
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class SemaphoreTest : TestBase() {

    @Test
    fun testSimple() = runTest {
        val semaphore = Semaphore(2)
        launch {
            expect(3)
            semaphore.release()
            expect(4)
        }
        expect(1)
        semaphore.acquire()
        semaphore.acquire()
        expect(2)
        semaphore.acquire()
        finish(5)
    }

    @Test
    fun testSimpleAsMutex() = runTest {
        val semaphore = Semaphore(1)
        expect(1)
        launch {
            expect(4)
            semaphore.acquire() // suspends
            expect(7) // now got lock
            semaphore.release()
            expect(8)
        }
        expect(2)
        semaphore.acquire() // locked
        expect(3)
        yield() // yield to child
        expect(5)
        semaphore.release()
        expect(6)
        yield() // now child has lock
        finish(9)
    }

    @Test
    fun tryAcquireTest() = runTest {
        val semaphore = Semaphore(2)
        assertTrue(semaphore.tryAcquire())
        assertTrue(semaphore.tryAcquire())
        assertFalse(semaphore.tryAcquire())
        assertEquals(0, semaphore.availablePermits)
        semaphore.release()
        assertEquals(1, semaphore.availablePermits)
        assertTrue(semaphore.tryAcquire())
        assertEquals(0, semaphore.availablePermits)
    }

    @Test
    fun withSemaphoreTest() = runTest {
        val semaphore = Semaphore(1)
        assertEquals(1, semaphore.availablePermits)
        semaphore.withPermit {
            assertEquals(0, semaphore.availablePermits)
        }
        assertEquals(1, semaphore.availablePermits)
    }

    @Test
    fun fairnessTest() = runTest {
        val semaphore = Semaphore(1)
        semaphore.acquire()
        launch(coroutineContext) {
            // first to acquire
            expect(2)
            semaphore.acquire() // suspend
            expect(6)
        }
        launch(coroutineContext) {
            // second to acquire
            expect(3)
            semaphore.acquire() // suspend
            expect(9)
        }
        expect(1)
        yield()
        expect(4)
        semaphore.release()
        expect(5)
        yield()
        expect(7)
        semaphore.release()
        expect(8)
        yield()
        finish(10)
    }

    @Test
    fun testCancellationReturnsPermitBack() = runTest {
        val semaphore = Semaphore(1)
        semaphore.acquire()
        assertEquals(0, semaphore.availablePermits)
        val job = launch {
            assertFalse(semaphore.tryAcquire())
            semaphore.acquire()
        }
        yield()
        job.cancelAndJoin()
        assertEquals(0, semaphore.availablePermits)
        semaphore.release()
        assertEquals(1, semaphore.availablePermits)
    }

    @Test
    fun testMultipleReleasesResumeMultipleAcquirers() = runTest {
        val permits = 5
        val semaphore = Semaphore(permits)
        semaphore.acquire(permits)
        assertEquals(0, semaphore.availablePermits)
        val jobs = mutableListOf<Deferred<Boolean>>()
        for (i in 0 until permits) {
            jobs += async {
                expect(2 + i)
                assertFalse(semaphore.tryAcquire())
                semaphore.acquire()
                expect(2 + permits + i)
                return@async true
            }
        }
        expect(1)
        yield()
        semaphore.release(permits)
        jobs.forEach {
            assertTrue(it.await())
        }
        assertEquals(0, semaphore.availablePermits)
        semaphore.release(permits)
        assertEquals(permits, semaphore.availablePermits)
        finish(1 + permits + permits + 1) // first + two iterations + last
    }

    @Test
    fun testSingleReleaseDoesNotResumeMultipleAcquirers() = runTest {
        val acquires = 5
        val permits = 5
        val semaphore = Semaphore(permits, permits)
        assertEquals(0, semaphore.availablePermits)
        val criticalSections = Array(acquires) { false }
        val jobs = mutableListOf<Job>()
        repeat(acquires) { i ->
            jobs += launch {
                expect(2 + i)
                semaphore.acquire(permits)
                criticalSections[i] = true
                expect(2 + i + acquires)
            }
        }
        expect(1)
        yield()
        assertEquals(0, semaphore.availablePermits)
        fun testFairness(i: Int) {
            for (k in 0 until i) {
                assertEquals(true, criticalSections[k])
            }
            for (k in i + 1 until acquires) {
                assertEquals(false, criticalSections[k])
            }
        }
        repeat(acquires) { i ->
            repeat(permits - 1) {
                semaphore.release()
                testFairness(i)
                assertEquals(0, semaphore.availablePermits)
            }
            semaphore.release()
            jobs[i].join()
            testFairness(i)
            assertEquals(0, semaphore.availablePermits)
        }
        semaphore.release(permits)
        assertEquals(permits, semaphore.availablePermits)
        finish(1 + acquires + acquires + 1)
    }

    @Test
    fun testCancellationDoesNotResumeWaitingAcquirers() = runTest {
        val semaphore = Semaphore(1)
        semaphore.acquire()
        val job1 = launch {
            // 1st job in the waiting queue
            expect(2)
            semaphore.acquire()
            expectUnreached()
        }
        val job2 = launch {
            // 2nd job in the waiting queue
            expect(3)
            semaphore.acquire()
            expectUnreached()
        }
        expect(1)
        yield()
        expect(4)
        job2.cancel()
        yield()
        expect(5)
        job1.cancel()
        finish(6)
    }

    @Test
    fun testAcquiredPermits() = runTest {
        val semaphore = Semaphore(5, acquiredPermits = 4)
        assertEquals(semaphore.availablePermits, 1)
        semaphore.acquire()
        assertEquals(semaphore.availablePermits, 0)
        assertFalse(semaphore.tryAcquire())
        semaphore.release()
        assertEquals(semaphore.availablePermits, 1)
        assertTrue(semaphore.tryAcquire())
    }

    @Test
    fun testMultipleAcquiredPermits() = runTest {
        val semaphore = Semaphore(5, acquiredPermits = 1)
        assertEquals(semaphore.availablePermits, 4)
        semaphore.acquire(4)
        assertEquals(semaphore.availablePermits, 0)
        assertFalse(semaphore.tryAcquire())
        semaphore.release()
        assertEquals(semaphore.availablePermits, 1)
        assertTrue(semaphore.tryAcquire())
    }

    @Test
    fun testReleaseAcquiredPermits() = runTest {
        val semaphore = Semaphore(5, acquiredPermits = 4)
        assertEquals(semaphore.availablePermits, 1)
        repeat(4) { semaphore.release() }
        assertEquals(5, semaphore.availablePermits)
        assertFailsWith<IllegalStateException> { semaphore.release() }
        repeat(5) { assertTrue(semaphore.tryAcquire()) }
        assertFalse(semaphore.tryAcquire())
    }

    @Test
    fun testReleaseMultipleAcquiredPermits() = runTest {
        val semaphore = Semaphore(5, acquiredPermits = 4)
        assertEquals(semaphore.availablePermits, 1)
        semaphore.release(2)
        assertEquals(3, semaphore.availablePermits)
        assertFailsWith<IllegalStateException> { semaphore.release(3) }
        repeat(3) { assertTrue(semaphore.tryAcquire()) }
        assertFalse(semaphore.tryAcquire())
    }

    @Test
    fun testIllegalArguments() = runTest {
        assertFailsWith<IllegalArgumentException> { Semaphore(-1, 0) }
        assertFailsWith<IllegalArgumentException> { Semaphore(0, 0) }
        assertFailsWith<IllegalArgumentException> { Semaphore(1, -1) }
        assertFailsWith<IllegalArgumentException> { Semaphore(1, 2) }
        val semaphore = Semaphore(1)
        assertFailsWith<IllegalArgumentException> { semaphore.acquire(-1) }
        assertFailsWith<IllegalArgumentException> { semaphore.tryAcquire(-1) }
        assertFailsWith<IllegalArgumentException> { semaphore.release(-1) }
    }
}