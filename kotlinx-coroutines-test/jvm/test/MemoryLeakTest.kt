/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
import kotlinx.coroutines.*
import kotlinx.coroutines.test.*
import java.lang.ref.*
import kotlin.test.*

class MemoryLeakTest {

    @Test
    fun testCancellationLeakInTestCoroutineScheduler() = runTest {
        lateinit var weakRef: WeakReference<*>
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            val leakingObject = Any()
            weakRef = WeakReference(leakingObject)
            delay(3)
            // This code is needed to hold a reference to `leakingObject` until the job itself is weakly reachable.
            leakingObject.hashCode()
        }
        job.cancel()
        System.gc()
        assertNotNull(weakRef.get()) // the cancellation handler has not run yet
        runCurrent()
        System.gc()
        assertNull(weakRef.get()) // the cancellation handler has run, disposing of the job
    }
}
