/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.native.concurrent.*

internal abstract class Thread {
    abstract fun execute(block: () -> Unit)
    abstract fun parkNanos(timeout: Long)
}

@ThreadLocal
private val currentThread: Thread = initCurrentThread()

internal fun currentThread(): Thread = currentThread

internal expect fun initCurrentThread(): Thread

internal expect fun Worker.toThread(): Thread

internal fun Worker.execute(block: () -> Unit) {
    block.freeze()
    executeAfter(0, block)
}

internal open class WorkerThread(val worker: Worker = Worker.current) : Thread() {
    override fun execute(block: () -> Unit) = worker.execute(block)

    override fun parkNanos(timeout: Long) {
        // Note: worker is parked in microseconds
        worker.park(timeout / 1000L, process = true)
    }

    override fun equals(other: Any?): Boolean = other is WorkerThread && other.worker == worker
    override fun hashCode(): Int = worker.hashCode()
    override fun toString(): String = worker.name
}

internal interface ThreadBoundInterceptor {
    val thread: Thread
}

internal fun ThreadBoundInterceptor.checkCurrentThread() {
    val current = currentThread()
    check(current == thread) { "This dispatcher can be used only from a single thread $thread, but now in $current" }
}