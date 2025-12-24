package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.coroutines.*
import kotlin.test.*

class LimitedParallelismUnhandledExceptionTest : TestBase() {

    @Test
    fun testUnhandledException() = runTest {
        var caughtException: Throwable? = null
        val executor = Executors.newFixedThreadPool(
            1
        ) {
            Thread(it).also {
                it.uncaughtExceptionHandler = Thread.UncaughtExceptionHandler { _, e -> caughtException = e }
            }
        }.asCoroutineDispatcher()
        val view = executor.limitedParallelism(1)
        view.dispatch(EmptyCoroutineContext, Runnable { throw TestException() })
        withContext(view) {
            // Verify it is in working state and establish happens-before
        }
        assertTrue { caughtException is TestException }
        executor.close()
    }
}
