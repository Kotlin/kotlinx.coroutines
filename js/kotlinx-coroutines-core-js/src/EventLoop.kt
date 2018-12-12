/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*

internal actual fun createEventLoop(): EventLoop = UnconfinedEventLoop()

internal class UnconfinedEventLoop : EventLoop() {
    private val queue = Queue<Runnable>()

    override val isEmpty: Boolean
        get() = queue.isEmpty

    override fun processNextEvent(): Long {
        queue.poll()?.run()
        return if (queue.isEmpty) Long.MAX_VALUE else 0L
    }

    override fun enqueue(task: Runnable): Boolean {
        queue.add(task)
        return true
    }
}
