package kotlinx.coroutines.test

import kotlin.test.*

@Suppress("DEPRECATION_ERROR")
class TestCoroutineExceptionHandlerTest {
    @Test
    fun whenExceptionsCaught_availableViaProperty() {
        val subject = TestCoroutineExceptionHandler()
        val expected = IllegalArgumentException()
        subject.handleException(subject, expected)
        assertEquals(listOf(expected), subject.uncaughtExceptions)
    }
}
