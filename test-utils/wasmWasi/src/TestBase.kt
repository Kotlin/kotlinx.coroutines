package kotlinx.coroutines.testing

import kotlin.test.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*

actual val VERBOSE = false

actual typealias NoWasmWasi = Ignore

actual val isStressTest: Boolean = false
actual val stressTestMultiplier: Int = 1
actual val stressTestMultiplierSqrt: Int = 1

actual typealias TestResult = Unit

internal actual fun lastResortReportException(error: Throwable) {
    println(error)
}

actual open class TestBase(
    private val errorCatching: ErrorCatching.Impl
): OrderedExecutionTestBase(), ErrorCatching by errorCatching {

    actual constructor(): this(errorCatching = ErrorCatching.Impl())

    actual fun println(message: Any?) {
        kotlin.io.println(message)
    }

    public actual fun runTest(
        expected: ((Throwable) -> Boolean)?,
        unhandled: List<(Throwable) -> Boolean>,
        block: suspend CoroutineScope.() -> Unit
    ): TestResult {
        var exCount = 0
        var ex: Throwable? = null
        try {
            runTestCoroutine(block = block, context = CoroutineExceptionHandler { _, e ->
                if (e is CancellationException) return@CoroutineExceptionHandler // are ignored
                exCount++
                when {
                    exCount > unhandled.size ->
                        error("Too many unhandled exceptions $exCount, expected ${unhandled.size}, got: $e", e)
                    !unhandled[exCount - 1](e) ->
                        error("Unhandled exception was unexpected: $e", e)
                }
            })
        } catch (e: Throwable) {
            ex = e
            if (expected != null) {
                if (!expected(e))
                    error("Unexpected exception: $e", e)
            } else
                throw e
        } finally {
            if (ex == null && expected != null) kotlin.error("Exception was expected but none produced")
        }
        if (exCount < unhandled.size)
            kotlin.error("Too few unhandled exceptions $exCount, expected ${unhandled.size}")
    }
}

actual val isNative = false

actual val isBoundByJsTestTimeout = true

actual val isJavaAndWindows: Boolean get() = false

actual val usesSharedEventLoop: Boolean = true
