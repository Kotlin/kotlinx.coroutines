package kotlinx.coroutines.experimental

import org.junit.Test
import java.util.concurrent.CountDownLatch
import java.util.concurrent.TimeUnit

class CoroutineExceptionHandlerTest {
    @Test
    fun testCoroutineExceptionHandlerCreator() {
        val latch = CountDownLatch(1)
        var coroutineException: Throwable? = null

        val handler = CoroutineExceptionHandler { _, ex ->
            coroutineException = ex
            latch.countDown()
        }

        launch(CommonPool + handler) {
            throw TestException()
        }

        latch.await(10, TimeUnit.SECONDS)

        check(coroutineException is TestException)
    }
}

private class TestException: RuntimeException()