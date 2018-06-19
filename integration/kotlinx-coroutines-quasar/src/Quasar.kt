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

package kotlinx.coroutines.experimental.quasar

import co.paralleluniverse.fibers.Fiber
import co.paralleluniverse.fibers.FiberAsync
import co.paralleluniverse.fibers.SuspendExecution
import co.paralleluniverse.fibers.Suspendable
import co.paralleluniverse.strands.SuspendableCallable
import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.CoroutineContext
import kotlin.coroutines.experimental.startCoroutine

/**
 * Runs Quasar-instrumented suspendable code from Kotlin coroutine.
 */
suspend fun <T> runSuspendable(callable: SuspendableCallable<T>): T = suspendCancellableCoroutine { cont ->
    val fiber = object : Fiber<Unit>() {
        @Throws(SuspendExecution::class)
        override fun run() {
            val result = try { callable.run() }
            catch (e: Throwable) {
                cont.resumeWithException(e)
                return
            }
            cont.resume(result)
        }
    }
    cont.cancelFutureOnCancellation(fiber)
    fiber.start()
}

/**
 * Runs Kotlin suspending function from Quasar-instrumented suspendable code.
 */
@Suspendable
fun <T> runFiberBlocking(block: suspend () -> T): T =
    CoroutineAsync(block).run()

private class CoroutineAsync<T>(
    private val block: suspend () -> T
) : FiberAsync<T, Throwable>(), Continuation<T> {
    override val context: CoroutineContext = Fiber.currentFiber().scheduler.executor.asCoroutineDispatcher()
    override fun resume(value: T) { asyncCompleted(value) }
    override fun resumeWithException(exception: Throwable) { asyncFailed(exception) }

    override fun requestAsync() {
        block.startCoroutine(completion = this)
    }
}
