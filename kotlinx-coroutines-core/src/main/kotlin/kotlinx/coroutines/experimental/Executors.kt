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
import java.util.concurrent.ExecutorService
import java.util.concurrent.ScheduledExecutorService
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Converts an instance of [Executor] to an implementation of [CoroutineDispatcher].
 */
public fun Executor.toCoroutineDispatcher(): CoroutineDispatcher =
    ExecutorCoroutineDispatcher(this)

internal open class ExecutorCoroutineDispatcher(val executor: Executor) : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) = executor.execute(block)

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        (executor as? ScheduledExecutorService ?: scheduledExecutor).scheduleResumeAfterDelay(time, unit, continuation)
    }
}

internal fun ExecutorService.scheduleResume(cont: CancellableContinuation<Unit>) {
    val future = submit { cont.resume(Unit) }
    cont.cancelFutureOnCompletion(future)
}

internal fun ScheduledExecutorService.scheduleResumeAfterDelay(time: Long, unit: TimeUnit, cont: CancellableContinuation<Unit>) {
    val timeout = schedule({ cont.resume(Unit) }, time, unit)
    cont.cancelFutureOnCompletion(timeout)
}
