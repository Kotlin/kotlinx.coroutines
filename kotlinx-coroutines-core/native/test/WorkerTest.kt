/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.native.concurrent.*
import kotlin.test.*

class WorkerTest : TestBase() {
    val worker = Worker.start()

    @AfterTest
    fun tearDown() {
        worker.requestTermination().result
    }

    @Test
    fun testLaunchInWorker() {
        worker.execute(TransferMode.SAFE, { }) {
            runBlocking {
                launch { }.join()
                delay(1)
                println("Done")
            }
        }.result
    }

    @Test
    fun testLaunchInWorkerTroughGlobalScope() {
        worker.execute(TransferMode.SAFE, { }) {
            runBlocking {
                CoroutineScope(EmptyCoroutineContext).launch {
                    delay(1)
                }.join()
            }
        }.result
    }
}
