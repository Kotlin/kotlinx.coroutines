package kotlinx.coroutines.sync

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import kotlin.test.*

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
    fun withSemaphoreOnFailureTest() = runTest {
        val semaphore = Semaphore(1)
        assertEquals(1, semaphore.availablePermits)
        try {
            semaphore.withPermit {
                assertEquals(0, semaphore.availablePermits)
                throw TestException()
            }
        } catch (e: TestException) {
            // Expected
        }
        assertEquals(1, semaphore.availablePermits)
    }

    @Test
    fun withSemaphoreOnEarlyReturnTest() = runTest {
        val semaphore = Semaphore(1)
        assertEquals(1, semaphore.availablePermits)
        suspend fun f() {
            semaphore.withPermit {
                assertEquals(0, semaphore.availablePermits)
                return@f
            }
        }
        f()
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

    @Test
    fun testWithPermitJsMiscompilation() = runTest {
        // This is a reproducer for KT-58685
        // On Kotlin/JS IR, the compiler miscompiles calls to 'release' in an inlined finally
        // This is visible on the withPermit function
        // Until the compiler bug is fixed, this test case checks that we do not suffer from it
        val semaphore = Semaphore(1)
        assertFailsWith<IndexOutOfBoundsException> {
            try {
                semaphore.withPermit { null } ?: throw IndexOutOfBoundsException() // should throw…
            } catch (e: Exception) {
                throw e // …but instead fails here
            }
        }
    }
}
