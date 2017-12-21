package kotlinx.coroutines.experimental

import kotlin.test.*

class CommonJobTest : TestBase() {
    @Test
    fun testState() {
        val job = Job()
        assertTrue(job.isActive)
        job.cancel()
        assertTrue(!job.isActive)
    }

    @Test
    fun testHandler() {
        val job = Job()
        var fireCount = 0
        job.invokeOnCompletion { fireCount++ }
        assertTrue(job.isActive)
        assertEquals(0, fireCount)
        // cancel once
        job.cancel()
        assertTrue(!job.isActive)
        assertEquals(1, fireCount)
        // cancel again
        job.cancel()
        assertTrue(!job.isActive)
        assertEquals(1, fireCount)
    }

    @Test
    fun testManyHandlers() {
        val job = Job()
        val n = 100 * stressTestMultiplier
        val fireCount = IntArray(n)
        for (i in 0 until n) job.invokeOnCompletion { fireCount[i]++ }
        assertTrue(job.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        // cancel once
        job.cancel()
        assertTrue(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        // cancel again
        job.cancel()
        assertTrue(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
    }

    @Test
    fun testUnregisterInHandler() {
        val job = Job()
        val n = 100 * stressTestMultiplier
        val fireCount = IntArray(n)
        for (i in 0 until n) {
            var registration: DisposableHandle? = null
            registration = job.invokeOnCompletion {
                fireCount[i]++
                registration!!.dispose()
            }
        }
        assertTrue(job.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        // cancel once
        job.cancel()
        assertTrue(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        // cancel again
        job.cancel()
        assertTrue(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
    }

    @Test
    fun testManyHandlersWithUnregister() {
        val job = Job()
        val n = 100 * stressTestMultiplier
        val fireCount = IntArray(n)
        val registrations = Array<DisposableHandle>(n) { i -> job.invokeOnCompletion { fireCount[i]++ } }
        assertTrue(job.isActive)
        fun unreg(i: Int) = i % 4 <= 1
        for (i in 0 until n) if (unreg(i)) registrations[i].dispose()
        for (i in 0 until n) assertEquals(0, fireCount[i])
        job.cancel()
        assertTrue(!job.isActive)
        for (i in 0 until n) assertEquals(if (unreg(i)) 0 else 1, fireCount[i])
    }

    @Test
    fun testExceptionsInHandler() {
        val job = Job()
        val n = 100 * stressTestMultiplier
        val fireCount = IntArray(n)
        class TestException : Throwable()
        for (i in 0 until n) job.invokeOnCompletion {
            fireCount[i]++
            throw TestException()
        }
        assertTrue(job.isActive)
        for (i in 0 until n) assertEquals(0, fireCount[i])
        val tryCancel = Try<Unit> { job.cancel() }
        assertTrue(!job.isActive)
        for (i in 0 until n) assertEquals(1, fireCount[i])
        assertTrue(tryCancel.exception is CompletionHandlerException)
        assertTrue(tryCancel.exception!!.cause is TestException)
    }

    @Test
    fun testCancelledParent() {
        val parent = Job()
        parent.cancel()
        assertTrue(!parent.isActive)
        val child = Job(parent)
        assertTrue(!child.isActive)
    }

    @Test
    fun testDisposeSingleHandler() {
        val job = Job()
        var fireCount = 0
        val handler = job.invokeOnCompletion { fireCount++ }
        handler.dispose()
        job.cancel()
        assertEquals(0, fireCount)
    }

    @Test
    fun testDisposeMultipleHandler() {
        val job = Job()
        val handlerCount = 10
        var fireCount = 0
        val handlers = Array(handlerCount) { job.invokeOnCompletion { fireCount++ } }
        handlers.forEach { it.dispose() }
        job.cancel()
        assertEquals(0, fireCount)
    }
}