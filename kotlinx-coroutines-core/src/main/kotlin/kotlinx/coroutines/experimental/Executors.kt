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
 */
public fun Executor.toCoroutineDispatcher(): CoroutineDispatcher =
    ExecutorCoroutineDispatcher(this)

internal open class ExecutorCoroutineDispatcher(val executor: Executor) : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) = executor.execute(block)

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        val timeout = if (executor is ScheduledExecutorService)
            executor.schedule(ResumeUndispatchedRunnable(this, continuation), time, unit) else
            scheduledExecutor.schedule(ResumeRunnable(continuation), time, unit)
        continuation.cancelFutureOnCompletion(timeout)
    }
}

// --- reusing these classes in other places ---

internal class ResumeUndispatchedRunnable(
    val dispatcher: CoroutineDispatcher,
    val continuation: CancellableContinuation<Unit>
) : Runnable {
    override fun run() {
        with(continuation) { dispatcher.resumeUndispatched(Unit) }
    }
}

internal class ResumeRunnable(val continuation: Continuation<Unit>) : Runnable {
    override fun run() {
        continuation.resume(Unit)
    }
}
