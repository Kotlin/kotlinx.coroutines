package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class CoroutineExceptionHandlerJvmTest : TestBase() {

    private val exceptionHandler = Thread.getDefaultUncaughtExceptionHandler()
    private lateinit var caughtException: Throwable

    @Before
    fun setUp() {
        Thread.setDefaultUncaughtExceptionHandler({ _, e -> caughtException = e })
    }

    @After
    fun tearDown() {
        Thread.setDefaultUncaughtExceptionHandler(exceptionHandler)
    }

    @Test
    fun testFailingHandler() = runBlocking {
        expect(1)
        val job = GlobalScope.launch(CoroutineExceptionHandler { _, _ -> throw AssertionError() }) {
            expect(2)
            throw TestException()
        }

        job.join()
        assertIs<RuntimeException>(caughtException)
        assertIs<AssertionError>(caughtException.cause)
        assertIs<TestException>(caughtException.suppressed[0])

        finish(3)
    }

    @Test
    fun testLastDitchHandlerContainsContextualInformation() = runBlocking {
        expect(1)
        GlobalScope.launch(CoroutineName("last-ditch")) {
            expect(2)
            throw TestException()
        }.join()
        assertIs<TestException>(caughtException)
        assertContains(caughtException.suppressed[0].toString(), "last-ditch")
        finish(3)
    }
}
