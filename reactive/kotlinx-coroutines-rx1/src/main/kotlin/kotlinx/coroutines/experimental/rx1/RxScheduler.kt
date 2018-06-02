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

package kotlinx.coroutines.experimental.rx1

import rx.Scheduler
import kotlinx.coroutines.experimental.CancellableContinuation
import kotlinx.coroutines.experimental.CoroutineDispatcher
import kotlinx.coroutines.experimental.Delay
import kotlinx.coroutines.experimental.DisposableHandle
import rx.Subscription
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Converts an instance of [Scheduler] to an implementation of [CoroutineDispatcher]
 * and provides native [delay][Delay.delay] support.
 */
public fun Scheduler.asCoroutineDispatcher() = SchedulerCoroutineDispatcher(this)

/**
 * Implements [CoroutineDispatcher] on top of an arbitrary [Scheduler].
 * @param scheduler a scheduler.
 */
public class SchedulerCoroutineDispatcher(private val scheduler: Scheduler) : CoroutineDispatcher(), Delay {
    override fun dispatch(context: CoroutineContext, block: Runnable) {
        scheduler.createWorker().schedule { block.run() }
    }

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) =
        scheduler.createWorker()
                .schedule({
                    with(continuation) { resumeUndispatched(Unit) }
                 }, time, unit)
                .let { subscription ->
                    continuation.unsubscribeOnCancellation(subscription)
                }

    override fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle =
        scheduler.createWorker().schedule({ block.run() }, time, unit).asDisposableHandle()

    private fun Subscription.asDisposableHandle(): DisposableHandle = object : DisposableHandle {
        override fun dispose() = unsubscribe()
    }

    override fun toString(): String = scheduler.toString()
    override fun equals(other: Any?): Boolean = other is SchedulerCoroutineDispatcher && other.scheduler === scheduler
    override fun hashCode(): Int = System.identityHashCode(scheduler)
}
