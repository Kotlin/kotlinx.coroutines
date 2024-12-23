package kotlinx.coroutines

import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.coroutines.intrinsics.*
import kotlin.test.*

class RunBlockingDispatchLocalTasksTest {

    // A coroutine deadlock occurs if there is a task in the local queue
    // of the blocking thread before it is parked by the nested runBlocking
    @Test(timeout = 1000)
    fun testEmptyLocalTasksBeforePark() {
        runBlocking(Dispatchers.IO) {
            val latch = CountDownLatch(1)
            lateinit var launchContinuation: Continuation<Unit>
            lateinit var runBlockingContinuation: Continuation<Unit>
            CoroutineScope(Dispatchers.IO).launch {
                suspendCoroutineUninterceptedOrReturn {
                    launchContinuation = it
                    latch.countDown()
                    COROUTINE_SUSPENDED
                }
                yield()
                runBlockingContinuation.resume(Unit)
            }
            latch.await()
            runBlocking {
                suspendCancellableCoroutine {
                    runBlockingContinuation = it
                    launchContinuation.resume(Unit)
                }
            }
        }
    }
}
