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
}
