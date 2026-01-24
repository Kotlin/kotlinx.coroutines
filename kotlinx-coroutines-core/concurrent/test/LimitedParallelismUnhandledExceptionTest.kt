//// Need to add concurrent UncaughtExceptionHandler
//package kotlinx.coroutines
//
//import kotlinx.coroutines.testing.*
//import kotlin.test.*
//import kotlin.coroutines.*
//
//class LimitedParallelismUnhandledExceptionTest : TestBase() {
//
//    @Test
//    fun testUnhandledException() = runTest {
//        var caughtException: Throwable? = null
////        val executor = Executors.newFixedThreadPool(
////            1
////        ) {
////            Thread(it).also {
////                it.uncaughtExceptionHandler = Thread.UncaughtExceptionHandler { _, e -> caughtException = e }
////            }
////        }.asCoroutineDispatcher()
//        newSingleThreadContext("test").use { executor ->
//            val view = executor.limitedParallelism(1)
//            view.dispatch(EmptyCoroutineContext) { throw TestException() }
//            withContext(view) {
//                // Verify it is in working state and establish happens-before
//            }
//            assertTrue { caughtException is TestException }
//        }
//    }
//}
