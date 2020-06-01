/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.native.concurrent.*
import kotlin.test.*

private const val timeoutMicroseconds = Long.MAX_VALUE / 1000L // too long.
private const val nTasks = 10_000 // repeat test

/**
 * This stress test ensures that Worker.park correctly wakes up.
 */
class ParkStressTest {
    @Test
    fun testPark() {
        val worker = Worker.start()
        worker.execute(TransferMode.SAFE, {}) {
            // process nTasks
            while (TaskCounter.counter < nTasks) {
                randomWait()
                val ok = Worker.current.park(timeoutMicroseconds, process = true)
                assertTrue(ok, "Must have processed a task")
            }
            assertEquals(nTasks, TaskCounter.counter)
        }
        // submit nTasks
        repeat(nTasks) { index ->
            randomWait()
            val operation: () -> Unit = {
                TaskCounter.counter++
            }
            operation.freeze()
            worker.executeAfter(0, operation)
        }
        // shutdown worker
        worker.requestTermination().result // block until termination
    }
}

@ThreadLocal
private object TaskCounter {
    var counter = 0
}

