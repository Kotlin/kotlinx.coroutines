package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.sync.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import kotlin.test.*

class MutexCancellationStressTest : TestBase() {
    @Test
    fun testStressCancellationDoesNotBreakMutex() = runTest {
        val mutex = Mutex()
        val mutexJobNumber = 3
        val mutexOwners = Array(mutexJobNumber) { "$it" }
        val dispatcher = Executors.newFixedThreadPool(mutexJobNumber + 2).asCoroutineDispatcher()
        var counter = 0
        val counterLocal = Array(mutexJobNumber) { AtomicInteger(0) }
        val completed = AtomicBoolean(false)
        val mutexJobLauncher: (jobNumber: Int) -> Job = { jobId ->
            val coroutineName = "MutexJob-$jobId"
            // ATOMIC to always have a chance to proceed
            launch(dispatcher + CoroutineName(coroutineName), CoroutineStart.ATOMIC) {
                while (!completed.get()) {
                    // Stress out holdsLock
                    mutex.holdsLock(mutexOwners[(jobId + 1) % mutexJobNumber])
                    // Stress out lock-like primitives
                    if (mutex.tryLock(mutexOwners[jobId])) {
                        counterLocal[jobId].incrementAndGet()
                        counter++
                        mutex.unlock(mutexOwners[jobId])
                    }
                    mutex.withLock(mutexOwners[jobId]) {
                        counterLocal[jobId].incrementAndGet()
                        counter++
                    }
                    select<Unit> {
                        mutex.onLock(mutexOwners[jobId]) {
                            counterLocal[jobId].incrementAndGet()
                            counter++
                            mutex.unlock(mutexOwners[jobId])
                        }
                    }
                }
            }
        }
        val mutexJobs = (0 until mutexJobNumber).map { mutexJobLauncher(it) }.toMutableList()
        val checkProgressJob = launch(dispatcher + CoroutineName("checkProgressJob")) {
            var lastCounterLocalSnapshot = (0 until mutexJobNumber).map { 0 }
            while (!completed.get()) {
                delay(500)
                // If we've caught the completion after delay, then there is a chance no progress were made whatsoever, bail out
                if (completed.get()) return@launch
                val c = counterLocal.map { it.get() }
                for (i in 0 until mutexJobNumber) {
                    assert(c[i] > lastCounterLocalSnapshot[i]) { "No progress in MutexJob-$i, last observed state: ${c[i]}" }
                }
                lastCounterLocalSnapshot = c
            }
        }
        val cancellationJob = launch(dispatcher + CoroutineName("cancellationJob")) {
            var cancellingJobId = 0
            while (!completed.get()) {
                val jobToCancel = mutexJobs.removeFirst()
                jobToCancel.cancelAndJoin()
                mutexJobs += mutexJobLauncher(cancellingJobId)
                cancellingJobId = (cancellingJobId + 1) % mutexJobNumber
            }
        }
        delay(2000L * stressTestMultiplier)
        completed.set(true)
        cancellationJob.join()
        mutexJobs.forEach { it.join() }
        checkProgressJob.join()
        assertEquals(counter, counterLocal.sumOf { it.get() })
        dispatcher.close()
    }
}
