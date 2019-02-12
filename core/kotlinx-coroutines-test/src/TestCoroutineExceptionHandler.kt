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
     * The returned list will be a copy of the currently caught exceptions.
     *
     * During [cleanupTestCoroutines] the first element of this list will be rethrown if it is not empty.
     */
    val exceptions: List<Throwable>

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
    val lock = Object()

    override fun handleException(context: CoroutineContext, exception: Throwable) {
        synchronized(lock) {
            _exceptions += exception
        }
    }

    override val key = CoroutineExceptionHandler

    private val _exceptions = mutableListOf<Throwable>()

    override val exceptions
        get() = _exceptions.toList()

    override fun cleanupTestCoroutines() {
        synchronized(lock) {
            val exception = _exceptions.firstOrNull() ?: return
            throw exception
        }
    }
}
