import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import kotlin.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

@Suppress("DEPRECATION", "DEPRECATION_ERROR")
class MultithreadingTest {

    @Test
    fun testSingleThreadExecutor() = runBlocking {
        val mainThread = Thread.currentThread()
        Dispatchers.setMain(Dispatchers.Unconfined)
        newSingleThreadContext("testSingleThread").use { threadPool ->
            withContext(Dispatchers.Main) {
                assertSame(mainThread, Thread.currentThread())
            }

            Dispatchers.setMain(threadPool)
            withContext(Dispatchers.Main) {
                assertNotSame(mainThread, Thread.currentThread())
            }
            assertSame(mainThread, Thread.currentThread())

            withContext(Dispatchers.Main.immediate) {
                assertNotSame(mainThread, Thread.currentThread())
            }
            assertSame(mainThread, Thread.currentThread())

            Dispatchers.setMain(Dispatchers.Unconfined)
            withContext(Dispatchers.Main.immediate) {
                assertSame(mainThread, Thread.currentThread())
            }
            assertSame(mainThread, Thread.currentThread())
        }
    }

    /** Tests that resuming the coroutine of [runTest] asynchronously in reasonable time succeeds. */
    @Test
    fun testResumingFromAnotherThread() = runTest {
        suspendCancellableCoroutine<Unit> { cont ->
            thread {
                Thread.sleep(10)
                cont.resume(Unit)
            }
        }
    }

    /** Tests that [StandardTestDispatcher] is not executed in-place but confined to the thread in which the
     * virtual time control happens. */
    @Test
    fun testStandardTestDispatcherIsConfined(): Unit = runBlocking {
        val scheduler = TestCoroutineScheduler()
        val initialThread = Thread.currentThread()
        val job = launch(StandardTestDispatcher(scheduler)) {
            assertEquals(initialThread, Thread.currentThread())
            withContext(Dispatchers.IO) {
                val ioThread = Thread.currentThread()
                assertNotSame(initialThread, ioThread)
            }
            assertEquals(initialThread, Thread.currentThread())
        }
        scheduler.advanceUntilIdle()
        while (job.isActive) {
            scheduler.receiveDispatchEvent()
            scheduler.advanceUntilIdle()
        }
    }
}
