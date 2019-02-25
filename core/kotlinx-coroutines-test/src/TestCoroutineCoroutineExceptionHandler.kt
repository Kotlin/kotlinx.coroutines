package kotlinx.coroutines.test

import kotlinx.coroutines.CoroutineExceptionHandler
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlin.coroutines.CoroutineContext

/**
 * Access uncaught coroutine exceptions captured during test execution.
 */
@ExperimentalCoroutinesApi
interface UncaughtExceptionCaptor {
    /**
     * List of uncaught coroutine exceptions.
     *
     * The returned list will be a copy of the currently caught exceptions.
     *
     * During [cleanupTestCoroutines] the first element of this list will be rethrown if it is not empty.
     */
    val uncaughtExceptions: List<Throwable>

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
@ExperimentalCoroutinesApi
class TestCoroutineCoroutineExceptionHandler: UncaughtExceptionCaptor, CoroutineExceptionHandler {

    override fun handleException(context: CoroutineContext, exception: Throwable) {
        synchronized(_exceptions) {
            _exceptions += exception
        }
    }

    override val key = CoroutineExceptionHandler

    private val _exceptions = mutableListOf<Throwable>()

    override val uncaughtExceptions
        get() = synchronized(_exceptions) { _exceptions.toList() }

    override fun cleanupTestCoroutines() {
        synchronized(_exceptions) {
            val exception = _exceptions.firstOrNull() ?: return
            throw exception
        }
    }
}
