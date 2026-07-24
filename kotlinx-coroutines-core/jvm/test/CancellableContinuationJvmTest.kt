package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import java.util.concurrent.atomic.AtomicBoolean
import kotlin.coroutines.*
import kotlin.test.*

class CancellableContinuationJvmTest : TestBase() {
    @Test
    fun testCoroutineOwnsVirtualThread() = runBlocking {
        val rootThread = Thread.currentThread()
        assertTrue(rootThread.isVirtualForTest())

        val deferred = async {
            val owner = Thread.currentThread()
            assertTrue(owner.isVirtualForTest())
            assertNotSame(rootThread, owner)
            delay(10)
            assertSame(owner, Thread.currentThread())
            42
        }
        assertEquals(42, deferred.await())

        val job = launch {
            assertTrue(Thread.currentThread().isVirtualForTest())
            awaitCancellation()
        }
        job.cancelAndJoin()
        assertTrue(job.isCancelled)
    }

    @Test
    fun testCancellableSuspensionBlocksVirtualThread() = runBlocking(Dispatchers.Default) {
        val coroutineThread = Thread.currentThread()
        assertTrue(Thread::class.java.getMethod("isVirtual").invoke(coroutineThread) as Boolean)
        val observedWaitingThread = AtomicBoolean()
        suspendCancellableCoroutine<Unit> { continuation ->
            Thread {
                val deadline = System.nanoTime() + 5_000_000_000L
                while (coroutineThread.state != Thread.State.WAITING && System.nanoTime() < deadline) {
                    Thread.yield()
                }
                observedWaitingThread.set(coroutineThread.state == Thread.State.WAITING)
                continuation.resume(Unit)
            }.start()
        }
        assertTrue(observedWaitingThread.get())
        assertSame(coroutineThread, Thread.currentThread())
    }

    @Test
    fun testToString() = runTest {
        checkToString()
    }

    private suspend fun checkToString() {
        suspendCancellableCoroutine<Unit> {
            it.resume(Unit)
            assertTrue(it.toString().contains("kotlinx.coroutines.CancellableContinuationJvmTest.checkToString(CancellableContinuationJvmTest.kt"))
        }
        yield() // Eliminate tail-call optimization
    }

    @Test
    fun testExceptionIsNotReported() = runTest({ it is CancellationException }) {
        val ctx = coroutineContext
        suspendCancellableCoroutine<Unit> {
            ctx.cancel()
            it.resumeWith(Result.failure(TestException()))
        }
    }

    @Test
    fun testBlockingIntegration() = runTest {
        val source = BlockingSource()
        val job = launch(Dispatchers.Default) {
            source.await()
        }
        source.cancelAndJoin(job)
    }

    @Test
    fun testBlockingIntegrationAlreadyCancelled() = runTest {
        val source = BlockingSource()
        val job = launch(Dispatchers.Default) {
            cancel()
            source.await()
        }
        source.cancelAndJoin(job)
    }

    private suspend fun BlockingSource.cancelAndJoin(job: Job) {
        while (!hasSubscriber) {
            Thread.sleep(10)
        }
        job.cancelAndJoin()
    }

    private suspend fun BlockingSource.await() = suspendCancellableCoroutine<Unit> {
        it.invokeOnCancellation { this.cancel() }
        subscribe()
    }

    private class BlockingSource {
        @Volatile
        private var isCancelled = false

        @Volatile
        var hasSubscriber = false

        fun subscribe() {
            hasSubscriber = true
            while (!isCancelled) {
                Thread.sleep(10)
            }
        }

        fun cancel() {
            isCancelled = true
        }
    }
}

private fun Thread.isVirtualForTest(): Boolean =
    Thread::class.java.getMethod("isVirtual").invoke(this) as Boolean
