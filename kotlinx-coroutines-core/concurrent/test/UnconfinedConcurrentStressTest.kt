//package kotlinx.coroutines
//
//import kotlinx.coroutines.testing.*
//import kotlin.test.*
//
//class UnconfinedConcurrentStressTest : TestBase() {
//    private val threads = 4
////    private val threadLocal = ThreadLocal<Int>()
//
//    @Test
//    fun testConcurrent() = runTest {
//        val iterations = 1_000 * stressTestMultiplier
//        val startBarrier = ConcurrentCyclicBarrier(threads + 1)
//        val finishLatch = ConcurrentCountDownLatch(threads)
//
//        newFixedThreadPoolContext(threads, "UnconfinedConcurrentStressTest").use { pool ->
//            repeat(threads) { id ->
//                launch(pool) {
//                    startBarrier.await()
//                    repeat(iterations) {
////                        threadLocal.set(0)
//                        launch(Dispatchers.Unconfined) {
////                            assertEquals(0, threadLocal.get())
//                            launch(Dispatchers.Unconfined) {
////                                assertEquals(id, threadLocal.get())
//                            }
////                            threadLocal.set(id)
//                        }
//                    }
//                    finishLatch.countDown()
//                }
//            }
//            startBarrier.await()
//            finishLatch.await()
//        }
//    }
//}
