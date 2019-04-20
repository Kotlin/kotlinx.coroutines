import kotlinx.coroutines.test.TestCoroutineExceptionHandler
import org.junit.Test
import kotlin.test.assertEquals

class TestCoroutineExceptionHandlerTest {
    @Test
    fun whenExceptionsCaught_avaliableViaProperty() {
        val subject = TestCoroutineExceptionHandler()
        val expected = IllegalArgumentException()
        subject.handleException(subject, expected)
        assertEquals(listOf(expected), subject.uncaughtExceptions)
    }
}