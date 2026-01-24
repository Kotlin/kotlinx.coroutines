//// Hangs
//
//package kotlinx.coroutines
//
//import kotlinx.atomicfu.atomic
//import kotlinx.coroutines.testing.*
//import kotlin.test.*
//
//class CancellableContinuationResumeCloseStressTest : TestBase() {
//    private val startBarrier = ConcurrentCyclicBarrier(3)
//    private val doneBarrier = ConcurrentCyclicBarrier(2)
//    private val nRepeats = 1_000 * stressTestMultiplier
//
//    private val closed = atomic(false)
//    private var returnedOk = false
//
//    @Test
//    fun testStress() = runTest {
//        newFixedThreadPoolContext(2, "test").use { pool ->
//            repeat(nRepeats) {
//                closed.value = false
//                returnedOk = false
//                val job = launchTestJob(pool)
//                startBarrier.await()
//                job.cancel() // (1) cancel job
//                job.join()
//                // check consistency
//                doneBarrier.await()
//                if (returnedOk) {
//                    assertFalse(closed.value, "should not have closed resource -- returned Ok")
//                } else {
//                    assertTrue(closed.value, "should have closed resource -- was cancelled")
//                }
//            }
//        }
//    }
//
//    private fun CoroutineScope.launchTestJob(dispatcher: CoroutineDispatcher): Job =
//        launch(dispatcher, start = CoroutineStart.ATOMIC) {
//            val ok = resumeClose() // might be cancelled
//            assertEquals("OK", ok)
//            returnedOk = true
//        }
//
//    private suspend fun CoroutineScope.resumeClose() = suspendCancellableCoroutine { cont ->
//        launch {
//            startBarrier.await() // (2) resume at the same time
//            cont.resume("OK") { _, _, _ ->
//                close()
//            }
//            doneBarrier.await()
//        }
//        startBarrier.await() // (3) return at the same time
//    }
//
//    fun close() {
//        assertFalse(closed.getAndSet(true))
//    }
//}
