/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import kotlin.coroutines.*
import kotlin.native.concurrent.*
import kotlin.test.*

class WorkerTest : TestBase() {

    @Test
    fun testLaunchInWorker() {
        val worker = Worker.start()
        worker.execute(TransferMode.SAFE, { }) {
            runBlocking {
                launch { }.join()
                delay(1)
            }
        }.result
        worker.requestTermination()
    }

    @Test
    fun testLaunchInWorkerThroughGlobalScope() {
        val worker = Worker.start()
        worker.execute(TransferMode.SAFE, { }) {
            runBlocking {
                CoroutineScope(EmptyCoroutineContext).launch {
                    delay(10)
                }.join()
            }
        }.result
        worker.requestTermination()
    }

    /**
     * Test that [runBlocking] does not crash after [Worker.requestTermination] is called on the worker that runs it.
     */
    @Test
    fun testRunBlockingInTerminatedWorker() {
        val workerInRunBlocking = Channel<Unit>()
        val workerTerminated = Channel<Unit>()
        val checkResumption = Channel<Unit>()
        val finished = Channel<Unit>()
        val worker = Worker.start()
        worker.executeAfter(0) {
            runBlocking {
                workerInRunBlocking.send(Unit)
                workerTerminated.receive()
                checkResumption.receive()
                finished.send(Unit)
            }
        }
        runBlocking {
            workerInRunBlocking.receive()
            worker.requestTermination()
            workerTerminated.send(Unit)
            checkResumption.send(Unit)
            finished.receive()
        }
    }

    /**
     * Test that [newFixedThreadPoolContext] does not allocate more dispatchers than it needs to.
     * Incidentally also tests that it will allocate enough workers for its needs. Otherwise, the test will hang.
     */
    @Test
    fun testNotAllocatingExtraDispatchers() {
        suspend fun spin(set: MutableSet<Worker>) {
            repeat(100) {
                set.add(Worker.current)
                delay(1)
            }
        }
        val dispatcher = newFixedThreadPoolContext(64, "test")
        try {
            runBlocking {
                val encounteredWorkers = mutableSetOf<Worker>()
                var canStart = false
                val coroutine1 = launch(dispatcher) {
                    while (!canStart) {
                        // intentionally empty
                    }
                    spin(encounteredWorkers)
                }
                val coroutine2 = launch(dispatcher) {
                    canStart = true
                    spin(encounteredWorkers)
                }
                listOf(coroutine1, coroutine2).joinAll()
                assertEquals(2, encounteredWorkers.size)
            }
        } finally {
            dispatcher.close()
        }
    }
}
