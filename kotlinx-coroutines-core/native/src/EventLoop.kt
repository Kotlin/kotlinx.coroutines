/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.cinterop.*
import kotlin.coroutines.*
import kotlin.native.concurrent.*
import kotlin.system.*

internal actual abstract class EventLoopImplPlatform: EventLoop() {
    protected actual fun unpark() {
        /*
         * Does nothing, because we only work with EventLoop in Kotlin/Native from a single thread where
         * it was created. All tasks that come from other threads are passed into the owner thread via
         * Worker.execute and its queueing mechanics.
         */
    }

    protected actual fun reschedule(now: Long, delayedTask: EventLoopImplBase.DelayedTask): Unit =
        loopWasShutDown()
}

internal class EventLoopImpl: EventLoopImplBase() {
    init { ensureNeverFrozen() }

    val shareable = ShareableEventLoop(StableRef.create(this), Worker.current)

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle =
        scheduleInvokeOnTimeout(timeMillis, block)

    override fun shutdown() {
        super.shutdown()
        shareable.ref.dispose()
    }
}

internal class ShareableEventLoop(
    val ref: StableRef<EventLoopImpl>,
    private val worker: Worker
) : CoroutineDispatcher(), Delay, ThreadBoundInterceptor {
    override val thread: Thread = WorkerThread(worker)

    init { freeze() }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        checkCurrentThread()
        ref.get().scheduleResumeAfterDelay(timeMillis, continuation)
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        checkCurrentThread()
        return ref.get().invokeOnTimeout(timeMillis, block, context)
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        checkCurrentThread()
        ref.get().dispatch(context, block)
    }

    override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> {
        checkCurrentThread()
        return ref.get().interceptContinuation(continuation)
    }

    override fun releaseInterceptedContinuation(continuation: Continuation<*>) {
        checkCurrentThread()
        ref.get().releaseInterceptedContinuation(continuation)
    }
}

internal actual fun createEventLoop(): EventLoop = EventLoopImpl()

internal actual fun nanoTime(): Long = getTimeNanos()
