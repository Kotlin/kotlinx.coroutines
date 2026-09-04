package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.testing.Barrier
import kotlin.native.concurrent.*
import kotlin.test.*
import kotlin.time.Duration.Companion.seconds

class MultithreadedDispatchersTest {
    /**
     * Test that [newFixedThreadPoolContext] does not allocate more dispatchers than it needs to.
     * Incidentally also tests that it will allocate enough workers for its needs. Otherwise, the test will hang.
     */
    @Test
    fun testNotAllocatingExtraDispatchers() {
        val barrier = Barrier(2)
        val lock = SynchronizedObject()
        suspend fun spin(set: MutableSet<Worker>) {
            repeat(100) {
                synchronized(lock) { set.add(Worker.current) }
                delay(1)
            }
        }
        val dispatcher = newFixedThreadPoolContext(64, "test")
        try {
            runBlocking {
                val encounteredWorkers = mutableSetOf<Worker>()
                val coroutine1 = launch(dispatcher) {
                    barrier.await()
                    spin(encounteredWorkers)
                }
                val coroutine2 = launch(dispatcher) {
                    barrier.await()
                    spin(encounteredWorkers)
                }
                listOf(coroutine1, coroutine2).joinAll()
                assertEquals(2, encounteredWorkers.size)
            }
        } finally {
            dispatcher.close()
        }
    }

    /**
     * Test that [newSingleThreadContext] will not wait for the cancelled scheduled coroutines before closing.
     */
    @Test
    fun timeoutsNotPreventingClosing(): Unit = runBlocking {
        val dispatcher = WorkerDispatcher("test")
        withContext(dispatcher) {
            withTimeout(5.seconds) {
            }
        }
        withTimeout(1.seconds) {
            dispatcher.close() // should not wait for the timeout
            yield()
        }
    }
}
