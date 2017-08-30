package kotlinx.coroutines.experimental

import org.junit.Test

class CoroutineExceptionHandlerTest : TestBase() {
    @Test
    fun testCoroutineExceptionHandlerCreator() = runBlocking {
        expect(1)
        var coroutineException: Throwable? = null
        val handler = CoroutineExceptionHandler { _, ex ->
            coroutineException = ex
            expect(3)
        }
        val job = launch(coroutineContext + handler) {
            throw TestException()
        }
        expect(2)
        job.join()
        finish(4)
        check(coroutineException is TestException)
    }
}

private class TestException: RuntimeException()