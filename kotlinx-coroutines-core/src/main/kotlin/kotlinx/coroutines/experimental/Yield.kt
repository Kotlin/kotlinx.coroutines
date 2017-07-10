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

import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED
import kotlin.coroutines.experimental.intrinsics.suspendCoroutineOrReturn

/**
 * Yields a thread (or thread pool) of the current coroutine dispatcher to other coroutines to run.
 * If the coroutine dispatcher does not have its own thread pool (like [Unconfined] dispatcher) then this
 * function does nothing, but checks if the coroutine [Job] was completed.
 * This suspending function is cancellable.
 * If the [Job] of the current coroutine is cancelled or completed when this suspending function is invoked or while
 * this function is waiting for dispatching, it resumes with [CancellationException].
 */
suspend fun yield(): Unit = suspendCoroutineOrReturn sc@ { cont ->
    val context = cont.context
    val job = context[Job]
    if (job != null && job.isCancelledOrCompleted) throw job.getCompletionException()
    if (cont !is DispatchedContinuation<Unit>) return@sc Unit
    if (!cont.dispatcher.isDispatchNeeded(context)) return@sc Unit
    cont.dispatchYield(Unit)
    COROUTINE_SUSPENDED
}
