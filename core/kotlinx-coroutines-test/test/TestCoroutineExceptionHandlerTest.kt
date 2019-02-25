import kotlinx.coroutines.test.TestCoroutineCoroutineExceptionHandler
import org.junit.Test
import kotlin.test.assertEquals

class TestCoroutineExceptionHandlerTest {
    @Test
    fun whenExceptionsCaught_avaliableViaProperty() {
        val subject = TestCoroutineCoroutineExceptionHandler()
        val expected = IllegalArgumentException()
        subject.handleException(subject, expected)
        assertEquals(listOf(expected), subject.uncaughtExceptions)
    }
}