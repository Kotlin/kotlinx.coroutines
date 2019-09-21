package kotlinx.coroutines.sync

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.assertEquals

class SemaphoreStressTest : TestBase() {

    @Test
    fun stressTestAsMutex() = runBlocking(Dispatchers.Default) {
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
    fun stressTest() = runBlocking(Dispatchers.Default) {
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
    fun stressCancellation() = runBlocking(Dispatchers.Default) {
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

    /**
     * This checks if repeated releases that race with cancellations put
     * the semaphore into an incorrect state where permits are leaked.
     */
    @Test
    fun stressReleaseCancelRace() = runTest {
        val n = 10_000 * stressTestMultiplier
        val semaphore = Semaphore(1, 1)
        newSingleThreadContext("SemaphoreStressTest").use { pool ->
            repeat (n) {
                // Initially, we hold the permit and no one else can `acquire`,
                // otherwise it's a bug.
                assertEquals(0, semaphore.availablePermits)
                var job1_entered_critical_section = false
                val job1 = launch(start = CoroutineStart.UNDISPATCHED) {
                    semaphore.acquire()
                    job1_entered_critical_section = true
                    semaphore.release()
                }
                // check that `job1` didn't finish the call to `acquire()`
                assertEquals(false, job1_entered_critical_section)
                val job2 = launch(pool) {
                    semaphore.release()
                }
                // Because `job2` executes in a separate thread, this
                // cancellation races with the call to `release()`.
                job1.cancelAndJoin()
                job2.join()
                assertEquals(1, semaphore.availablePermits)
                semaphore.acquire()
            }
        }
    }

}
