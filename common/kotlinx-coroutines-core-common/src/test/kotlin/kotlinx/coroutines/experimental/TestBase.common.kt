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

import kotlin.test.*

public expect open class TestBase constructor() {
    public val isStressTest: Boolean
    public val stressTestMultiplier: Int

    public fun error(message: Any, cause: Throwable? = null): Nothing
    public fun expect(index: Int)
    public fun expectUnreached()
    public fun finish(index: Int)

    public fun runTest(
        expected: ((Throwable) -> Boolean)? = null,
        unhandled: List<(Throwable) -> Boolean> = emptyList(),
        block: suspend CoroutineScope.() -> Unit
    )
}

suspend inline fun <reified T : Exception> assertFailsWith(deferred: Deferred<*>) {
    try {
        deferred.await()
        fail("Expected ${T::class} to be thrown, but was completed successfully")
    } catch (e: Exception) {
        assertTrue(e is T, "Expected exception of type ${T::class}, but has $e}")
    }
}

// Clashes with assertFailsWith
suspend inline fun <reified T : Throwable> assertFails(noinline block: suspend () -> Unit): T {
    try {
        block()
        fail("Expected ${T::class} to be thrown, but was completed successfully")
    } catch (e: Throwable) {
        assertTrue(e is T, "Expected exception of type ${T::class}, but has $e}")
        return e as T
    }
}
