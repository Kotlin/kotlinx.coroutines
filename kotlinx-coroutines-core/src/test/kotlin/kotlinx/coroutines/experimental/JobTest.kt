package kotlinx.coroutines.experimental

import org.junit.Assert.*
import org.junit.Test

class JobTest {
    @Test
    fun testState() {
        val job = JobSupport()
        assertTrue(job.isActive)
        job.cancel()
        assertFalse(job.isActive)
    }

    @Test
    fun testHandler() {
        val job = JobSupport()
        var fireCount = 0
        job.onCompletion { fireCount++ }
        assertTrue(job.isActive)
        assertEquals(0, fireCount)
        // cancel once
        job.cancel()
        assertFalse(job.isActive)
        assertEquals(1, fireCount)
        // cancel again
        job.cancel()
        assertFalse(job.isActive)
        assertEquals(1, fireCount)
    }

    @Test
    fun testManyHandlers() {
        val job = JobSupport()
        val n = 100
        val fireCount = IntArray(n)
        for (i in 0 until n) job.onCompletion { fireCount[i]++ }
        assertTrue(job.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        // cancel once
        job.cancel()
        assertFalse(job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        // cancel again
        job.cancel()
        assertFalse(job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
    }

    @Test
    fun testUnregisterInHandler() {
        val job = JobSupport()
        val n = 100
        val fireCount = IntArray(n)
        for (i in 0 until n) {
            var registration: Job.Registration? = null
            registration = job.onCompletion {
                fireCount[i]++
                registration!!.unregister()
            }
        }
        assertTrue(job.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        // cancel once
        job.cancel()
        assertFalse(job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        // cancel again
        job.cancel()
        assertFalse(job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
    }

    @Test
    fun testManyHandlersWithUnregister() {
        val job = JobSupport()
        val n = 100
        val fireCount = IntArray(n)
        val registrations = Array<Job.Registration>(n) { i -> job.onCompletion { fireCount[i]++ } }
        assertTrue(job.isActive)
        fun unreg(i: Int) = i % 4 <= 1
        for (i in 0 until n) if (unreg(i)) registrations[i].unregister()
        for (i in 0 until n) assertEquals(0, fireCount[i])
        job.cancel()
        assertFalse(job.isActive)
        for (i in 0 until n) assertEquals(if (unreg(i)) 0 else 1, fireCount[i])
    }

    @Test
    fun testExceptionsInHandler() {
        val job = JobSupport()
        val n = 100
        val fireCount = IntArray(n)
        class TestException : Throwable()
        for (i in 0 until n) job.onCompletion {
            fireCount[i]++
            throw TestException()
        }
        assertTrue(job.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        val tryCancel = Try<Unit> { job.cancel() }
        assertFalse(job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        assertTrue(tryCancel.exception is TestException)
    }

    @Test
    fun testMemoryRelease() {
        val job = JobSupport()
        val n = 10_000_000
        var fireCount = 0
        for (i in 0 until n) job.onCompletion { fireCount++ }.unregister()
    }
}