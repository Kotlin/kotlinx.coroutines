/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

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
    }

    @Test
    fun testLaunchInWorkerTroughGlobalScope() {
        val worker = Worker.start()
        worker.execute(TransferMode.SAFE, { }) {
            runBlocking {
                CoroutineScope(EmptyCoroutineContext).launch {
                    delay(1)
                }.join()
            }
        }.result
    }
}
