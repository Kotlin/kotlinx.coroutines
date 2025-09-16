package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class CoroutineExceptionHandlerJvmTest : TestBase() {

    @Test
    fun testFailingHandler() = runBlocking {
        expect(1)
        val caughtException = catchingUncaughtException {
            GlobalScope.launch(CoroutineExceptionHandler { _, _ -> throw AssertionError() }) {
                expect(2)
                throw TestException()
            }.join()
        }
        assertIs<RuntimeException>(caughtException)
        assertIs<AssertionError>(caughtException.cause)
        assertIs<TestException>(caughtException.suppressed[0])

        finish(3)
    }

    @Test
    fun testLastDitchHandlerContainsContextualInformation() = runBlocking {
        expect(1)
        val caughtException = catchingUncaughtException {
            GlobalScope.launch(CoroutineName("last-ditch")) {
                expect(2)
                throw TestException()
            }.join()
        }
        assertIs<TestException>(caughtException)
        assertContains(caughtException.suppressed[0].toString(), "last-ditch")
        finish(3)
    }

    @Test
    fun testFailingUncaughtExceptionHandler() = runBlocking {
        expect(1)
        withUncaughtExceptionHandler({ _, e ->
            expect(3)
            throw TestException("uncaught")
        }) {
            launch(Job()) {
                expect(2)
                throw TestException("to be reported")
            }.join()
        }
        finish(4)
    }
}

private inline fun catchingUncaughtException(action: () -> Unit): Throwable? {
    var caughtException: Throwable? = null
    withUncaughtExceptionHandler({ _, e -> caughtException = e }) {
        action()
    }
    return caughtException
}

private inline fun <T> withUncaughtExceptionHandler(handler: Thread.UncaughtExceptionHandler, action: () -> T): T {
    val exceptionHandler = Thread.getDefaultUncaughtExceptionHandler()
    Thread.setDefaultUncaughtExceptionHandler(handler)
    try {
        return action()
    } finally {
        Thread.setDefaultUncaughtExceptionHandler(exceptionHandler)
    }
}
