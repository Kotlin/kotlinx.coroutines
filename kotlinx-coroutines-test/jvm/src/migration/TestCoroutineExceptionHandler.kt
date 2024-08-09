package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

internal class TestCoroutineExceptionHandler :
    AbstractCoroutineContextElement(CoroutineExceptionHandler), CoroutineExceptionHandler {
    private val _exceptions = mutableListOf<Throwable>()
    private val _lock = SynchronizedObject()
    private var _coroutinesCleanedUp = false

    @Suppress("INVISIBLE_MEMBER", "INVISIBLE_REFERENCE") // do not remove the INVISIBLE_REFERENCE suppression: required in K2
    override fun handleException(context: CoroutineContext, exception: Throwable) {
        synchronized(_lock) {
            if (_coroutinesCleanedUp) {
                handleUncaughtCoroutineException(context, exception)
            }
            _exceptions += exception
        }
    }

    val uncaughtExceptions: List<Throwable>
        get() = synchronized(_lock) { _exceptions.toList() }

    fun cleanupTestCoroutines() {
        synchronized(_lock) {
            _coroutinesCleanedUp = true
            val exception = _exceptions.firstOrNull() ?: return
            // log the rest
            _exceptions.drop(1).forEach { it.printStackTrace() }
            throw exception
        }
    }
}
