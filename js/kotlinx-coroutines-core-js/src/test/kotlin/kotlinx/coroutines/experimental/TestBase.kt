/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import kotlin.js.*

public actual open class TestBase actual constructor() {
    public actual val isStressTest: Boolean = false
    public actual val stressTestMultiplier: Int = 1

    private var actionIndex = 0
    private var finished = false
    private var error: Throwable? = null

    /**
     * Throws [IllegalStateException] like `error` in stdlib, but also ensures that the test will not
     * complete successfully even if this exception is consumed somewhere in the test.
     */
    public actual fun error(message: Any, cause: Throwable? = null): Nothing {
        if (cause != null) console.log(cause)
        val exception = IllegalStateException(
            if (cause == null) message.toString() else "$message; caused by $cause")
        if (error == null) error = exception
        throw exception
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

    // todo: The dynamic (promise) result is a work-around for missing suspend tests, see KT-22228
    public actual fun runTest(
        expected: ((Throwable) -> Boolean)? = null,
        unhandled: List<(Throwable) -> Boolean> = emptyList(),
        block: suspend CoroutineScope.() -> Unit
    ): dynamic {
        var exCount = 0
        var ex: Throwable? = null
        return promise(block = block, context = CoroutineExceptionHandler { context, e ->
            if (e is CancellationException) return@CoroutineExceptionHandler // are ignored
            exCount++
            if (exCount > unhandled.size)
                error("Too many unhandled exceptions $exCount, expected ${unhandled.size}", e)
            if (!unhandled[exCount - 1](e))
                error("Unhandled exception was unexpected", e)
            context[Job]?.cancel(e)
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
    }
}

private fun <T> Promise<T>.finally(block: () -> Unit): Promise<T> =
    then(onFulfilled = { value -> block(); value }, onRejected = { ex -> block(); throw ex })
