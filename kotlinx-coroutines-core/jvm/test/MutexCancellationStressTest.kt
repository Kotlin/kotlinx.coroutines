/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlinx.coroutines.sync.*
import org.junit.*
import java.util.concurrent.*

class MutexCancellationStressTest : TestBase() {
    @Test
    fun testStressCancellationDoesNotBreakMutex() = runTest {
        val mutex = Mutex()
        val mutexJobNumber = 3
        val mutexOwners = Array(mutexJobNumber) { "$it" }
        val dispatcher = Executors.newFixedThreadPool(mutexJobNumber + 2).asCoroutineDispatcher()
        var counter = 0
        val counterLocal = Array(mutexJobNumber) { LocalAtomicInt(0) }
        val completed = LocalAtomicInt(0)
        val mutexJobLauncher: (jobNumber: Int) -> Job = { jobId ->
            val coroutineName = "MutexJob-$jobId"
            launch(dispatcher + CoroutineName(coroutineName)) {
                while (completed.value == 0) {
                    mutex.holdsLock(mutexOwners[(jobId + 1) % mutexJobNumber])
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
            while (completed.value == 0) {
                delay(1000)
                val c = counterLocal.map { it.value }
                for (i in 0 until mutexJobNumber) {
                    assert(c[i] > lastCounterLocalSnapshot[i]) { "No progress in MutexJob-$i" }
                }
                lastCounterLocalSnapshot = c
            }
        }
        val cancellationJob = launch(dispatcher + CoroutineName("cancellationJob")) {
            var cancellingJobId = 0
            while (completed.value == 0) {
                val jobToCancel = mutexJobs.removeFirst()
                jobToCancel.cancelAndJoin()
                mutexJobs += mutexJobLauncher(cancellingJobId)
                cancellingJobId = (cancellingJobId + 1) % mutexJobNumber
            }
        }
        delay(2000L * stressTestMultiplier)
        completed.value = 1
        cancellationJob.join()
        mutexJobs.forEach { it.join() }
        checkProgressJob.join()
        check(counter == counterLocal.sumOf { it.value })
        dispatcher.close()
    }
}
