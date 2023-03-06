/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.Test
import java.util.concurrent.CountDownLatch
import java.util.concurrent.atomic.AtomicReference
import kotlin.coroutines.*

// Stresses scenario from #3613
class ReusableCancellableContinuationInvariantStressTest : TestBase() {

    // Tests have a timeout 10 sec because the bug they catch leads to an infinite spin-loop

    @Test(timeout = 10_000)
    fun testExceptionFromSuspendReusable() = doTest { /* nothing */ }


    @Test(timeout = 10_000)
    fun testExceptionFromCancelledSuspendReusable() = doTest { it.cancel() }


    @Suppress("SuspendFunctionOnCoroutineScope")
    private inline fun doTest(crossinline block: (Job) -> Unit) {
        runTest {
            repeat(10_000) {
                val latch = CountDownLatch(1)
                val continuationToResume = AtomicReference<Continuation<Unit>?>(null)
                val j1 = launch(Dispatchers.Default) {
                    latch.await()
                    suspendCancellableCoroutineReusable {
                        continuationToResume.set(it)
                        block(coroutineContext.job)
                        throw CancellationException() // Don't let getResult() chance to execute
                    }
                }

                val j2 = launch(Dispatchers.Default) {
                    latch.await()
                    while (continuationToResume.get() == null) {
                        // spin
                    }
                    continuationToResume.get()!!.resume(Unit)
                }

                latch.countDown()
                joinAll(j1, j2)
            }
        }
    }
}
