package kotlinx.coroutines.experimental

import kotlin.test.*

class CommonCoroutineExceptionHandlerTest : TestBase() {
    @Test
    fun testCoroutineExceptionHandlerCreator() = runTest {
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
        assertTrue(coroutineException is TestException)
    }

    private class TestException: RuntimeException()
}
