/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import kotlin.test.*

class MemoryLeakTest {

    @Test
    fun testCancellationLeakInTestCoroutineScheduler() = runTest {
        val leakingObject = Any()
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            delay(1)
            // This code is needed to hold a reference to `leakingObject` until the job itself is weakly reachable.
            leakingObject.hashCode()
        }
        job.cancel()
        FieldWalker.assertReachableCount(1, testScheduler) { it === leakingObject }
        runCurrent()
        FieldWalker.assertReachableCount(0, testScheduler) { it === leakingObject }
    }
}
