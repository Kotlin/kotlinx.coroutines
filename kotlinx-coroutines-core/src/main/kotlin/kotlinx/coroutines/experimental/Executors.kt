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

import java.util.concurrent.Executor
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Converts an instance of [Executor] to an implementation of [CoroutineDispatcher].
 * @suppress **Deprecated**: Renamed to [asCoroutineDispatcher].
 */
@Deprecated("Renamed to `asCoroutineDispatcher`",
    replaceWith = ReplaceWith("asCoroutineDispatcher()"))
public fun Executor.toCoroutineDispatcher(): CoroutineDispatcher =
    ExecutorCoroutineDispatcher(this)

/**
 * Converts an instance of [Executor] to an implementation of [CoroutineDispatcher].
 */
public fun Executor.asCoroutineDispatcher(): CoroutineDispatcher =
    ExecutorCoroutineDispatcher(this)

private class ExecutorCoroutineDispatcher(
    private val executor: Executor
) : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) = executor.execute(block)

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        val timeout = if (executor is ScheduledExecutorService)
            executor.schedule(ResumeUndispatchedRunnable(this, continuation), time, unit) else
            scheduledExecutor.schedule(ResumeRunnable(continuation), time, unit)
        continuation.cancelFutureOnCompletion(timeout)
    }

    override fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle {
        val timeout = if (executor is ScheduledExecutorService)
            executor.schedule(block, time, unit) else
            scheduledExecutor.schedule(block, time, unit)
        return DisposableFutureHandle(timeout)
    }

    override fun toString(): String = executor.toString()
    override fun equals(other: Any?): Boolean = other is ExecutorCoroutineDispatcher && other.executor === executor
    override fun hashCode(): Int = System.identityHashCode(executor)
}

// --- reusing these classes in other places ---

internal class ResumeUndispatchedRunnable(
    private val dispatcher: CoroutineDispatcher,
    private val continuation: CancellableContinuation<Unit>
) : Runnable {
    override fun run() {
        with(continuation) { dispatcher.resumeUndispatched(Unit) }
    }
}

internal class ResumeRunnable(
    private val continuation: Continuation<Unit>
) : Runnable {
    override fun run() {
        continuation.resume(Unit)
    }
}
