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
    fun testCancellationDoesNotResumeWaitingAcquirers() = runTest {
        val semaphore = Semaphore(1)
        semaphore.acquire()
        val job1 = launch { // 1st job in the waiting queue
            expect(2)
            semaphore.acquire()
            expectUnreached()
        }
        val job2 = launch { // 2nd job in the waiting queue
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
    fun testIllegalArguments() {
        assertFailsWith<IllegalArgumentException> { Semaphore(-1, 0) }
        assertFailsWith<IllegalArgumentException> { Semaphore(0, 0) }
        assertFailsWith<IllegalArgumentException> { Semaphore(1, -1) }
        assertFailsWith<IllegalArgumentException> { Semaphore(1, 2) }
    }
}