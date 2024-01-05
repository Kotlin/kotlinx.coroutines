package kotlinx.coroutines.testing.exceptions

import kotlinx.coroutines.*
import java.io.*
import java.util.*
import kotlin.contracts.*
import kotlin.coroutines.*
import kotlin.test.*

inline fun <reified T : Throwable> checkException(exception: Throwable) {
    assertIs<T>(exception)
    assertTrue(exception.suppressed.isEmpty())
    assertNull(exception.cause)
}

fun checkCycles(t: Throwable) {
    val sw = StringWriter()
    t.printStackTrace(PrintWriter(sw))
    assertFalse(sw.toString().contains("CIRCULAR REFERENCE"))
}

class CapturingHandler : AbstractCoroutineContextElement(CoroutineExceptionHandler),
    CoroutineExceptionHandler
{
    private var unhandled: ArrayList<Throwable>? = ArrayList()

    override fun handleException(context: CoroutineContext, exception: Throwable) = synchronized<Unit>(this) {
        unhandled!!.add(exception)
    }

    fun getException(): Throwable = synchronized(this) {
        val size = unhandled!!.size
        assert(size == 1) { "Expected one unhandled exception, but have $size: $unhandled" }
        return unhandled!![0].also { unhandled = null }
    }
}

fun captureExceptionsRun(
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> Unit
): Throwable {
    val handler = CapturingHandler()
    runBlocking(context + handler, block = block)
    return handler.getException()
}

@OptIn(ExperimentalContracts::class)
suspend inline fun <reified E: Throwable> assertCallsExceptionHandlerWith(
    crossinline operation: suspend (CoroutineExceptionHandler) -> Unit): E {
    contract {
        callsInPlace(operation, InvocationKind.EXACTLY_ONCE)
    }
    val handler = CapturingHandler()
    return withContext(handler) {
        operation(handler)
        assertIs<E>(handler.getException())
    }
}
