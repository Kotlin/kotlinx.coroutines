@file:OptIn(ExperimentalThreadBlockingApi::class)

package kotlinx.coroutines

import kotlinx.atomicfu.*
import kotlinx.atomicfu.locks.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.testing.*
import kotlin.test.*
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.nanoseconds

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
            // try to receive this string in a blocking way:
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

//    @Test
//    fun testEventLoopInDefaultExecutor() = runTest {
//        expect(1)
//        withContext(Dispatchers.Unconfined) {
//            delay(1)
//            assertTrue(Thread.currentThread().name.startsWith(DefaultExecutor.THREAD_NAME))
//            expect(2)
//            // now runBlocking inside default executor thread --> should use outer event loop
//            DefaultExecutor.enqueue {
//                expect(4) // will execute when runBlocking runs loop
//            }
//            expect(3)
//            runBlocking {
//                expect(5)
//            }
//        }
//        finish(6)
//    }

    @Test
    fun testSecondThreadRunBlocking() = runTest {
        val testThread = ParkingSupport.currentThreadHandle()
        val testContext = coroutineContext
        val event = EventSync() // will signal completion
        val thread = runThread {
            runBlocking { // outer event loop
                // Produce string "OK"
                val ch = produce { send("OK") }
                // try to receive this string in a blocking way using test context (another thread)
                assertEquals("OK", runBlocking(testContext) {
                    assertEquals(testThread, ParkingSupport.currentThreadHandle())
                    ch.receive() // it should not hang here
                })
            }
            event.fireEvent() // done thread
        }
        event.blockingAwait() // wait for the thread to complete
        thread.join() // it is safe to join the thread now
    }

    /**
     * Tests that, when delayed tasks are due on an event loop, they will execute earlier than the newly scheduled
     * non-delayed tasks.
     */
    @Test
    fun testPendingDelayedBeingDueEarlier() = runTest {
        launch(start = CoroutineStart.UNDISPATCHED) {
            delay(1)
            expect(1)
        }
        concurrentSleep(100.milliseconds)
        yield()
        finish(2)
    }

    class EventSync {
        private val waitingThread = atomic<ParkingHandle?>(null)
        private val fired = atomic(false)

        fun fireEvent() {
            fired.value = true
            waitingThread.value?.let { ParkingSupport.unpark(it) }
        }

        fun blockingAwait() {
            check(waitingThread.getAndSet(ParkingSupport.currentThreadHandle()) == null)
            while (!fired.getAndSet(false)) {
                val time = ThreadLocalEventLoop.currentOrNull()?.processNextEvent() ?: Long.MAX_VALUE
                ParkingSupport.park(time.nanoseconds)
            }
            waitingThread.value = null
        }
    }
}
