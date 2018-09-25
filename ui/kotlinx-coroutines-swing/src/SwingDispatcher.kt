/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.swing

import kotlinx.coroutines.experimental.*
import java.awt.event.*
import java.util.concurrent.*
import javax.swing.*
import kotlin.coroutines.experimental.*

/**
 * Dispatches execution onto Swing event dispatching thread and provides native [delay] support.
 */
public val Dispatchers.Swing : SwingDispatcher
    get() = kotlinx.coroutines.experimental.swing.Swing

/**
 * Dispatcher for Swing event dispatching thread.
 *
 * This class provides type-safety and a point for future extensions.
 */
public sealed class SwingDispatcher : CoroutineDispatcher(), Delay

/**
 * Dispatches execution onto Swing event dispatching thread and provides native [delay] support.
 * @suppress **Deprecated**: Use [Dispatchers.Swing].
 */
@Deprecated(
    message = "Use Dispatchers.Swing",
    replaceWith = ReplaceWith("Dispatchers.Swing",
        imports = ["kotlinx.coroutines.experimental.Dispatchers", "kotlinx.coroutines.experimental.swing.Swing"])
)
// todo: it will become an internal implementation object
object Swing : SwingDispatcher() {
    override fun dispatch(context: CoroutineContext, block: Runnable) = SwingUtilities.invokeLater(block)

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val timer = schedule(timeMillis, TimeUnit.MILLISECONDS, ActionListener {
            with(continuation) { resumeUndispatched(Unit) }
        })
        continuation.invokeOnCancellation { timer.stop() }
    }

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

    override fun toString() = "Swing"
}
