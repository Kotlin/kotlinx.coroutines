package kotlinx.coroutines.sync

import kotlinx.coroutines.*
import org.junit.Test
import org.junit.After
import kotlin.test.assertEquals

class SemaphoreStressTest : TestBase() {

    private val pool = newSingleThreadContext("SemaphoreStressTest")

    @After
    fun tearDown() {
        pool.close()
    }

    @Test
    fun stressTestAsMutex() = runTest {
        val n = 10_000 * stressTestMultiplier
        val k = 100
        var shared = 0
        val semaphore = Semaphore(1)
        val jobs = List(n) {
            launch {
                repeat(k) {
                    semaphore.acquire()
                    shared++
                    semaphore.release()
                }
            }
        }
        jobs.forEach { it.join() }
        assertEquals(n * k, shared)
    }

    @Test
    fun stressTest() = runTest {
        val n = 10_000 * stressTestMultiplier
        val k = 100
        val semaphore = Semaphore(10)
        val jobs = List(n) {
            launch {
                repeat(k) {
                    semaphore.acquire()
                    semaphore.release()
                }
            }
        }
        jobs.forEach { it.join() }
    }

    @Test
    fun stressCancellation() = runTest {
        val n = 10_000 * stressTestMultiplier
        val semaphore = Semaphore(1)
        semaphore.acquire()
        repeat(n) {
            val job = launch {
                semaphore.acquire()
            }
            yield()
            job.cancelAndJoin()
        }
        assertEquals(0, semaphore.availablePermits)
        semaphore.release()
        assertEquals(1, semaphore.availablePermits)
    }

    @Test
    fun stressReleaseCancellation() = runTest {
        val n = 10_000 * stressTestMultiplier
        val semaphore = Semaphore(1, 1)
        repeat (n) {
            assertEquals(0, semaphore.availablePermits)

            var shared = false

            val job1 = launch(pool) {
                semaphore.acquire()
                shared = true
                semaphore.release()
            }

            assertEquals(false, shared)

            val job2 = launch(pool) {
                semaphore.release()
            }

            job1.cancelAndJoin()
            job2.join()

            assertEquals(1, semaphore.availablePermits)
            semaphore.acquire()
        }

        pool.close()
    }

}
