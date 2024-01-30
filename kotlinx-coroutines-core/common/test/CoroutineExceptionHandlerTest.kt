package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlin.test.*

class CoroutineExceptionHandlerTest : TestBase() {
    // Parent Job() does not handle exception --> handler is invoked on child crash
    @Test
    fun testJob() = runTest {
        expect(1)
        var coroutineException: Throwable? = null
        val handler = CoroutineExceptionHandler { _, ex ->
            coroutineException = ex
            expect(3)
        }
        val parent = Job()
        val job = launch(handler + parent) {
            throw TestException()
        }
        expect(2)
        job.join()
        finish(4)
        assertIs<TestException>(coroutineException)
        assertTrue(parent.isCancelled)
    }

    // Parent CompletableDeferred() "handles" exception --> handler is NOT invoked on child crash
    @Test
    fun testCompletableDeferred() = runTest {
        expect(1)
        val handler = CoroutineExceptionHandler { _, _ ->
            expectUnreached()
        }
        val parent = CompletableDeferred<Unit>()
        val job = launch(handler + parent) {
            throw TestException()
        }
        expect(2)
        job.join()
        finish(3)
        assertTrue(parent.isCancelled)
        assertIs<TestException>(parent.getCompletionExceptionOrNull())
    }
}
