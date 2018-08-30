/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
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
    override val context: CoroutineContext =
        newCoroutineContext(Fiber.currentFiber().scheduler.executor.asCoroutineDispatcher())
    override fun resume(value: T) { asyncCompleted(value) }
    override fun resumeWithException(exception: Throwable) { asyncFailed(exception) }

    override fun requestAsync() {
        block.startCoroutine(completion = this)
    }
}
