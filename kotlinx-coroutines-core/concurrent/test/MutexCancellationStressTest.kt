@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines

import kotlinx.coroutines.selects.*
import kotlinx.coroutines.sync.*
import kotlinx.coroutines.testing.*
import kotlin.concurrent.atomics.*
import kotlin.test.*

class MutexCancellationStressTest : TestBase() {
    @Test
    fun testStressCancellationDoesNotBreakMutex() = runTest {
        val mutex = Mutex()
        val mutexJobNumber = 3
        val mutexOwners = Array(mutexJobNumber) { "$it" }
        val dispatcher = newFixedThreadPoolContext(mutexJobNumber + 2, name = "test")
        var counter = 0
        val counterLocal = Array(mutexJobNumber) { AtomicInt(0) }
        val completed = AtomicBoolean(false)
        val mutexJobLauncher: (jobNumber: Int) -> Job = { jobId ->
            val coroutineName = "MutexJob-$jobId"
            // ATOMIC to always have a chance to proceed
            launch(dispatcher + CoroutineName(coroutineName), CoroutineStart.ATOMIC) {
                while (!completed.load()) {
                    // Stress out holdsLock
                    mutex.holdsLock(mutexOwners[(jobId + 1) % mutexJobNumber])
                    // Stress out lock-like primitives
                    if (mutex.tryLock(mutexOwners[jobId])) {
                        counterLocal[jobId].incrementAndFetch()
                        counter++
                        mutex.unlock(mutexOwners[jobId])
                    }
                    mutex.withLock(mutexOwners[jobId]) {
                        counterLocal[jobId].incrementAndFetch()
                        counter++
                    }
                    @Suppress("DEPRECATION") select<Unit> {
                        mutex.onLock(mutexOwners[jobId]) {
                            counterLocal[jobId].incrementAndFetch()
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
            while (!completed.load()) {
                delay(500)
                // If we've caught the completion after delay, then there is a chance no progress were made whatsoever, bail out
                if (completed.load()) return@launch
                val c = counterLocal.map { it.load() }
                for (i in 0 until mutexJobNumber) {
                    assertTrue(c[i] > lastCounterLocalSnapshot[i], "No progress in MutexJob-$i, last observed state: ${c[i]}")
                }
                lastCounterLocalSnapshot = c
            }
        }
        val cancellationJob = launch(dispatcher + CoroutineName("cancellationJob")) {
            var cancellingJobId = 0
            while (!completed.load()) {
                val jobToCancel = mutexJobs.removeFirst()
                jobToCancel.cancelAndJoin()
                mutexJobs += mutexJobLauncher(cancellingJobId)
                cancellingJobId = (cancellingJobId + 1) % mutexJobNumber
            }
        }
        delay(2000L * stressTestMultiplier)
        completed.store(true)
        cancellationJob.join()
        mutexJobs.forEach { it.join() }
        checkProgressJob.join()
        assertEquals(counter, counterLocal.sumOf { it.load() })
        dispatcher.close()
    }
}
