package kotlinx.coroutines.experimental

import org.junit.Assert.*
import org.junit.Test

class JobTest {
    @Test
    fun testState() {
        val lifetime = JobSupport()
        assertTrue(lifetime.isActive)
        lifetime.cancel()
        assertFalse(lifetime.isActive)
    }

    @Test
    fun testHandler() {
        val lifetime = JobSupport()
        var fireCount = 0
        lifetime.onCompletion { fireCount++ }
        assertTrue(lifetime.isActive)
        assertEquals(0, fireCount)
        // cancel once
        lifetime.cancel()
        assertFalse(lifetime.isActive)
        assertEquals(1, fireCount)
        // cancel again
        lifetime.cancel()
        assertFalse(lifetime.isActive)
        assertEquals(1, fireCount)
    }

    @Test
    fun testManyHandlers() {
        val lifetime = JobSupport()
        val n = 100
        val fireCount = IntArray(n)
        for (i in 0 until n) lifetime.onCompletion { fireCount[i]++ }
        assertTrue(lifetime.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        // cancel once
        lifetime.cancel()
        assertFalse(lifetime.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        // cancel again
        lifetime.cancel()
        assertFalse(lifetime.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
    }

    @Test
    fun testUnregisterInHandler() {
        val lifetime = JobSupport()
        val n = 100
        val fireCount = IntArray(n)
        for (i in 0 until n) {
            var registration: Job.Registration? = null
            registration = lifetime.onCompletion {
                fireCount[i]++
                registration!!.unregister()
            }
        }
        assertTrue(lifetime.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        // cancel once
        lifetime.cancel()
        assertFalse(lifetime.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        // cancel again
        lifetime.cancel()
        assertFalse(lifetime.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
    }

    @Test
    fun testManyHandlersWithUnregister() {
        val lifetime = JobSupport()
        val n = 100
        val fireCount = IntArray(n)
        val registrations = Array<Job.Registration>(n) { i -> lifetime.onCompletion { fireCount[i]++ } }
        assertTrue(lifetime.isActive)
        fun unreg(i: Int) = i % 4 <= 1
        for (i in 0 until n) if (unreg(i)) registrations[i].unregister()
        for (i in 0 until n) assertEquals(0, fireCount[i])
        lifetime.cancel()
        assertFalse(lifetime.isActive)
        for (i in 0 until n) assertEquals(if (unreg(i)) 0 else 1, fireCount[i])
    }

    @Test
    fun testExceptionsInHandler() {
        val lifetime = JobSupport()
        val n = 100
        val fireCount = IntArray(n)
        class TestException : Throwable()
        for (i in 0 until n) lifetime.onCompletion {
            fireCount[i]++
            throw TestException()
        }
        assertTrue(lifetime.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        val tryCancel = `try`<Unit> { lifetime.cancel() }
        assertFalse(lifetime.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        assertTrue(tryCancel.exception is TestException)
    }

    @Test
    fun testMemoryRelease() {
        val lifetime = JobSupport()
        val n = 10_000_000
        var fireCount = 0
        for (i in 0 until n) lifetime.onCompletion { fireCount++ }.unregister()
    }
}