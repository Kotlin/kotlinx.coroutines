package kotlinx.coroutines.exceptions

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class CoroutineExceptionHandlerJvmTest : TestBase() {

    @Test
    fun testThrowingHandler() = runBlocking {
        expect(1)
        val caughtException = catchingUncaughtException {
            GlobalScope.launch(CoroutineExceptionHandler { _, _ -> throw TestException2() }) {
                expect(2)
                throw TestException()
            }.join()
        }
        assertIs<RuntimeException>(caughtException)
        assertIs<TestException2>(caughtException.cause)
        assertIs<TestException>(caughtException.suppressed[0])

        finish(3)
    }

    @Test
    fun testLastResortHandlerContainsContextualInformation() = runBlocking {
        expect(1)
        val caughtException = catchingUncaughtException {
            GlobalScope.launch(CoroutineName("last-resort")) {
                expect(2)
                throw TestException()
            }.join()
        }
        assertIs<TestException>(caughtException)
        assertContains(caughtException.suppressed[0].toString(), "last-resort")
        finish(3)
    }

    @Test
    fun testThrowingUncaughtExceptionHandler() = runBlocking {
        expect(1)
        withUncaughtExceptionHandler({ _, e ->
            // should be above the `expect` so that we can observe the failure
            assertIs<TestException>(e)
            expect(3)
            throw TestException("will not be reported")
        }) {
            launch(Job()) {
                expect(2)
                throw TestException("will be passed to the uncaught exception handler")
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
