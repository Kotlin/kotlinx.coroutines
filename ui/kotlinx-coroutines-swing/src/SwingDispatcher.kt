/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.swing

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.awt.event.*
import java.util.concurrent.*
import javax.swing.*
import kotlin.coroutines.*

/**
 * Dispatches execution onto Swing event dispatching thread and provides native [delay] support.
 */
@Suppress("unused")
public val Dispatchers.Swing : SwingDispatcher
    get() = kotlinx.coroutines.swing.Swing

/**
 * Dispatcher for Swing event dispatching thread.
 *
 * This class provides type-safety and a point for future extensions.
 */
public sealed class SwingDispatcher : MainCoroutineDispatcher(), Delay {
    /** @suppress */
    override fun dispatch(context: CoroutineContext, block: Runnable): Unit = SwingUtilities.invokeLater(block)

    /** @suppress */
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val timer = schedule(timeMillis, TimeUnit.MILLISECONDS, ActionListener {
            with(continuation) { resumeUndispatched(Unit) }
        })
        continuation.invokeOnCancellation { timer.stop() }
    }

    /** @suppress */
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        val timer = schedule(timeMillis, TimeUnit.MILLISECONDS, ActionListener {
            block.run()
        })
        return object : DisposableHandle {
            override fun dispose() {
                timer.stop()
            }
        }
    }

    private fun schedule(time: Long, unit: TimeUnit, action: ActionListener): Timer =
        Timer(unit.toMillis(time).coerceAtMost(Int.MAX_VALUE.toLong()).toInt(), action).apply {
            isRepeats = false
            start()
        }
}

internal class SwingDispatcherFactory : MainDispatcherFactory {
    override val loadPriority: Int
        get() = 0

    override fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher = Swing
}

private object ImmediateSwingDispatcher : SwingDispatcher() {
    override val immediate: MainCoroutineDispatcher
        get() = this

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = !SwingUtilities.isEventDispatchThread()

    override fun toString() = "Swing [immediate]"
}

/**
 * Dispatches execution onto Swing event dispatching thread and provides native [delay] support.
 */
internal object Swing : SwingDispatcher() {
    override val immediate: MainCoroutineDispatcher
        get() = ImmediateSwingDispatcher

    override fun toString() = "Swing"
}
