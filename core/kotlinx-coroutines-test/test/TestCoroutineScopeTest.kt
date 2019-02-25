import kotlinx.coroutines.CoroutineExceptionHandler
import kotlinx.coroutines.newSingleThreadContext
import kotlinx.coroutines.test.TestCoroutineScope
import org.junit.Test
import kotlin.test.assertFails

class TestCoroutineScopeTest {
    @Test
    fun whenGivenInvalidExceptionHandler_throwsException() {
        val handler = CoroutineExceptionHandler {  _, _ -> Unit }
        assertFails {
            TestCoroutineScope(handler)
        }
    }

    @Test
    fun whenGivenInvalidDispatcher_throwsException() {
        assertFails {
            TestCoroutineScope(newSingleThreadContext("incorrect call"))
        }
    }
}
