/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

internal object WasiDispatcher: CoroutineDispatcher(), Delay {
    override fun limitedParallelism(parallelism: Int): CoroutineDispatcher {
        parallelism.checkParallelism()
        return this
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        registerEvent(0) { block.run() }
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        val event = registerEvent(delayToNanos(timeMillis)) { block.run() }
        return DisposableHandle { event.cancel() }
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val event = registerEvent(delayToNanos(timeMillis)) {
            with(continuation) { resumeUndispatched(Unit) }
        }
        continuation.invokeOnCancellation(handler = { event.cancel() })
    }
}