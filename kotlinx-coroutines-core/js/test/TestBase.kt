/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.js.*

public actual val isStressTest: Boolean = false
public actual val stressTestMultiplier: Int = 1

@Suppress("ACTUAL_WITHOUT_EXPECT", "ACTUAL_TYPE_ALIAS_TO_CLASS_WITH_DECLARATION_SITE_VARIANCE")
public actual typealias TestResult = Promise<Unit>

public actual open class TestBase actual constructor() {
    public actual val isBoundByJsTestTimeout = true
    private var actionIndex = 0
    private var finished = false
    private var error: Throwable? = null
    private var lastTestPromise: Promise<*>? = null

    /**
     * Throws [IllegalStateException] like `error` in stdlib, but also ensures that the test will not
     * complete successfully even if this exception is consumed somewhere in the test.
     */
    @Suppress("ACTUAL_FUNCTION_WITH_DEFAULT_ARGUMENTS")
    public actual fun error(message: Any, cause: Throwable? = null): Nothing {
        if (cause != null) console.log(cause)
        val exception = IllegalStateException(
            if (cause == null) message.toString() else "$message; caused by $cause")
        if (error == null) error = exception
        throw exception
    }

    private fun printError(message: String, cause: Throwable) {
        if (error == null) error = cause
        println("$message: $cause")
        console.log(cause)
    }

    /**
     * Asserts that this invocation is `index`-th in the execution sequence (counting from one).
     */
    public actual fun expect(index: Int) {
        val wasIndex = ++actionIndex
        check(index == wasIndex) { "Expecting action index $index but it is actually $wasIndex" }
    }

    /**
     * Asserts that this line is never executed.
     */
    public actual fun expectUnreached() {
        error("Should not be reached")
    }

    /**
     * Asserts that this it the last action in the test. It must be invoked by any test that used [expect].
     */
    public actual fun finish(index: Int) {
        expect(index)
        check(!finished) { "Should call 'finish(...)' at most once" }
        finished = true
    }

    /**
     * Asserts that [finish] was invoked
     */
    public actual fun ensureFinished() {
        require(finished) { "finish(...) should be caller prior to this check" }
    }

    public actual fun reset() {
        check(actionIndex == 0 || finished) { "Expecting that 'finish(...)' was invoked, but it was not" }
        actionIndex = 0
        finished = false
    }

    @Suppress("ACTUAL_FUNCTION_WITH_DEFAULT_ARGUMENTS")
    public actual fun runTest(
        expected: ((Throwable) -> Boolean)? = null,
        unhandled: List<(Throwable) -> Boolean> = emptyList(),
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
        val result = GlobalScope.promise(block = block, context = CoroutineExceptionHandler { context, e ->
            if (e is CancellationException) return@CoroutineExceptionHandler // are ignored
            exCount++
            when {
                exCount > unhandled.size ->
                    printError("Too many unhandled exceptions $exCount, expected ${unhandled.size}, got: $e", e)
                !unhandled[exCount - 1](e) ->
                    printError("Unhandled exception was unexpected: $e", e)
            }
        }).catch { e ->
            ex = e
            if (expected != null) {
                if (!expected(e))
                    error("Unexpected exception", e)
            } else
                throw e
        }.finally {
            if (ex == null && expected != null) error("Exception was expected but none produced")
            if (exCount < unhandled.size)
                error("Too few unhandled exceptions $exCount, expected ${unhandled.size}")
            error?.let { throw it }
            check(actionIndex == 0 || finished) { "Expecting that 'finish(...)' was invoked, but it was not" }
        }
        lastTestPromise = result
        return result
    }
}

private fun <T> Promise<T>.finally(block: () -> Unit): Promise<T> =
    then(onFulfilled = { value -> block(); value }, onRejected = { ex -> block(); throw ex })
