import kotlinx.coroutines.CoroutineExceptionHandler
import kotlinx.coroutines.newSingleThreadContext
import kotlinx.coroutines.test.TestCoroutineDispatcher
import kotlinx.coroutines.test.TestCoroutineCoroutineExceptionHandler
import kotlinx.coroutines.test.TestCoroutineScope
import org.junit.Test

class TestCoroutineScopeTest {
    @Test(expected = IllegalArgumentException::class)
    fun whenGivenInvalidExceptionHandler_throwsException() {
        val handler = CoroutineExceptionHandler {  _, _ -> Unit }
        val subject = TestCoroutineScope(handler)
    }

    @Test(expected = IllegalArgumentException::class)
    fun whenGivenInvalidDispatcher_throwsException() {
        val subject = TestCoroutineScope(newSingleThreadContext("incorrect call"))
    }

    @Test(expected = IllegalArgumentException::class)
    fun whenCancelAllActions_callsCleanupTestCoroutines() {
        val handler = TestCoroutineCoroutineExceptionHandler()
        val subject = TestCoroutineScope(handler + TestCoroutineDispatcher())
        handler.handleException(handler, IllegalArgumentException())
        subject.cancelAllActions()
    }
}