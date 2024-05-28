package kotlinx.coroutines.testing

import kotlin.test.*
import kotlin.js.*
import kotlinx.coroutines.*

actual val VERBOSE = false

actual typealias NoWasmJs = Ignore

actual val isStressTest: Boolean = false
actual val stressTestMultiplier: Int = 1
actual val stressTestMultiplierSqrt: Int = 1

@JsName("Promise")
external class MyPromise : JsAny {
    fun then(onFulfilled: ((JsAny?) -> Unit), onRejected: ((JsAny) -> Unit)): MyPromise
    fun then(onFulfilled: ((JsAny?) -> Unit)): MyPromise
}

/** Always a `Promise<Unit>` */
public actual typealias TestResult = MyPromise

internal actual fun lastResortReportException(error: Throwable) {
    println(error)
}

actual open class TestBase(
    private val errorCatching: ErrorCatching.Impl
): OrderedExecutionTestBase(), ErrorCatching by errorCatching {
    private var lastTestPromise: Promise<JsAny?>? = null

    actual constructor(): this(errorCatching = ErrorCatching.Impl())

    actual fun println(message: Any?) {
        kotlin.io.println(message)
    }

    actual fun runTest(
        expected: ((Throwable) -> Boolean)?,
        unhandled: List<(Throwable) -> Boolean>,
        block: suspend CoroutineScope.() -> Unit
    ): TestResult {
        var exCount = 0
        var ex: Throwable? = null
        /*
         * This is an additional sanity check against `runTest` mis-usage on JS.
         * The only way to write an async test on JS is to return Promise from the test function.
         * _Just_ launching promise and returning `Unit` won't suffice as the underlying test framework
         * won't be able to detect an asynchronous failure in a timely manner.
         * We cannot detect such situations, but we can detect the most common erroneous pattern
         * in our code base, an attempt to use multiple `runTest` in the same `@Test` method,
         * which typically is a premise to the same error:
         * ```
         * @Test
         * fun incorrectTestForJs() { // <- promise is not returned
         *     for (parameter in parameters) {
         *         runTest {
         *             runTestForParameter(parameter)
         *         }
         *     }
         * }
         * ```
         */
        if (lastTestPromise != null) {
            error("Attempt to run multiple asynchronous test within one @Test method")
        }
        val result = GlobalScope.promise(block = block, context = CoroutineExceptionHandler { _, e ->
            if (e is CancellationException) return@CoroutineExceptionHandler // are ignored
            exCount++
            when {
                exCount > unhandled.size ->
                    error("Too many unhandled exceptions $exCount, expected ${unhandled.size}, got: $e", e)
                !unhandled[exCount - 1](e) ->
                    error("Unhandled exception was unexpected: $e", e)
            }
        }).catch { jsE ->
            val e = jsE.toThrowableOrNull() ?: error("Unexpected non-Kotlin exception $jsE")
            ex = e
            if (expected != null) {
                if (!expected(e)) {
                    println(e)
                    error("Unexpected exception $e", e)
                }
            } else
                throw e
            null
        }.finally {
            if (ex == null && expected != null) error("Exception was expected but none produced")
            if (exCount < unhandled.size)
                error("Too few unhandled exceptions $exCount, expected ${unhandled.size}")
            errorCatching.close()
            checkFinishCall()
        }
        lastTestPromise = result
        return result.unsafeCast()
    }
}

actual val isNative = false

actual val isBoundByJsTestTimeout = true

actual val isJavaAndWindows: Boolean get() = false

actual val usesSharedEventLoop: Boolean = false
