@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.concurrent.atomics.*
import kotlin.coroutines.*
import kotlin.coroutines.cancellation.CancellationException
import kotlin.test.*

// Stresses scenario from #3613
class ReusableCancellableContinuationInvariantStressTest : TestBase() {

    // Tests have a timeout 10 sec because the bug they catch leads to an infinite spin-loop

    //    @Test(timeout = 10_000)
    @Test
    fun testExceptionFromSuspendReusable() = doTest { /* nothing */ }


    //    @Test(timeout = 10_000)
    @Test
    fun testExceptionFromCancelledSuspendReusable() = doTest { it.cancel() }


    @Suppress("SuspendFunctionOnCoroutineScope")
    private inline fun doTest(crossinline block: (Job) -> Unit) {
        runTest {
            repeat(10_000) {
                val latch = ConcurrentCountDownLatch(1)
                val continuationToResume = AtomicReference<Continuation<Unit>?>(null)
                val j1 = launch(Dispatchers.Default) {
                    latch.await()
                    suspendCancellableCoroutineReusable {
                        continuationToResume.store(it)
                        block(coroutineContext.job)
                        throw CancellationException() // Don't let getResult() chance to execute
                    }
                }

                val j2 = launch(Dispatchers.Default) {
                    latch.await()
                    while (continuationToResume.load() == null) {
                        // spin
                    }
                    continuationToResume.load()!!.resume(Unit)
                }

                latch.countDown()
                joinAll(j1, j2)
            }
        }
    }
}
