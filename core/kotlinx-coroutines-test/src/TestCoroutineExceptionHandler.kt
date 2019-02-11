package kotlinx.coroutines.test

import kotlinx.coroutines.CoroutineExceptionHandler
import java.util.*
import kotlin.coroutines.CoroutineContext

/**
 * Access uncaught coroutines exceptions captured during test execution.
 *
 * Note, tests executed via [runBlockingTest] or [TestCoroutineScope.runBlocking] will not trigger uncaught exception
 * handling and should use [Deferred.await] or [Job.getCancellationException] to test exceptions.
 */
interface ExceptionCaptor {
    /**
     * List of uncaught coroutine exceptions.
     *
     * During [cleanupTestCoroutines] the first element of this list will be rethrown if it is not empty.
     */
    val exceptions: MutableList<Throwable>

    /**
     * Call after the test completes.
     *
     * @throws Throwable the first uncaught exception, if there are any uncaught exceptions
     */
    fun cleanupTestCoroutines()
}

/**
 * An exception handler that can be used to capture uncaught exceptions in tests.
 */
class TestCoroutineExceptionHandler: ExceptionCaptor, CoroutineExceptionHandler {
    override fun handleException(context: CoroutineContext, exception: Throwable) {
        exceptions += exception
    }

    override val key = CoroutineExceptionHandler

    override val exceptions = LinkedList<Throwable>()

    override fun cleanupTestCoroutines() {
        val exception = exceptions.firstOrNull() ?: return
        throw exception
    }
}
