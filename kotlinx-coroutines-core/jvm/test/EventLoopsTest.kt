package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlinx.atomicfu.*
import kotlinx.coroutines.channels.*
import org.junit.Test
import java.util.concurrent.locks.*
import kotlin.concurrent.*
import kotlin.test.*

/**
 * Tests event loops integration.
 * See [https://github.com/Kotlin/kotlinx.coroutines/issues/860].
 */
class EventLoopsTest : TestBase() {
    @Test
    fun testNestedRunBlocking() {
        runBlocking { // outer event loop
            // Produce string "OK"
            val ch = produce { send("OK") }
            // try receive this string in a blocking way:
            assertEquals("OK", runBlocking { ch.receive() }) // it should not hang here
        }
    }

    @Test
    fun testUnconfinedInRunBlocking() {
        var completed = false
        runBlocking {
            launch(Dispatchers.Unconfined) {
                completed = true
            }
            // should not go into runBlocking loop, but complete here
            assertTrue(completed)
        }
    }

    @Test
    fun testNestedUnconfined() {
        expect(1)
        GlobalScope.launch(Dispatchers.Unconfined) {
            expect(2)
            GlobalScope.launch(Dispatchers.Unconfined) {
                // this gets scheduled into the outer unconfined loop
                expect(4)
            }
            expect(3) // ^^ executed before the above unconfined
        }
        finish(5)
    }

    @Test
    fun testSecondThreadRunBlocking() = runTest {
        val testThread = Thread.currentThread()
        val testContext = coroutineContext
        val event = EventSync() // will signal completion
        val thread = thread {
            runBlocking { // outer event loop
                // Produce string "OK"
                val ch = produce { send("OK") }
                // try receive this string in a blocking way using test context (another thread)
                assertEquals("OK", runBlocking(testContext) {
                    assertEquals(testThread, Thread.currentThread())
                    ch.receive() // it should not hang here
                })
            }
            event.fireEvent() // done thread
        }
        event.blockingAwait() // wait for the thread to complete
        thread.join() // it is safe to join the thread now
    }

    /**
     * Tests that, when delayed tasks are due on an event loop, they will execute earlier than the newly-scheduled
     * non-delayed tasks.
     */
    @Test
    fun testPendingDelayedBeingDueEarlier() = runTest {
        launch(start = CoroutineStart.UNDISPATCHED) {
            delay(1)
            expect(1)
        }
        Thread.sleep(100)
        yield()
        finish(2)
    }

    class EventSync {
        private val waitingThread = atomic<Thread?>(null)
        private val fired = atomic(false)

        fun fireEvent() {
            fired.value = true
            waitingThread.value?.let { LockSupport.unpark(it) }
        }

        fun blockingAwait() {
            check(waitingThread.getAndSet(Thread.currentThread()) == null)
            while (!fired.getAndSet(false)) {
                val time = ThreadLocalEventLoop.currentOrNull()?.tryUseAsEventLoop()?.processNextEvent()
                    ?: Long.MAX_VALUE
                LockSupport.parkNanos(time)
            }
            waitingThread.value = null
        }
    }
}
