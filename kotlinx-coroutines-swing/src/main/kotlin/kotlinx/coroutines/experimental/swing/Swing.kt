package kotlinx.coroutines.experimental.swing

import kotlinx.coroutines.experimental.CancellableContinuation
import kotlinx.coroutines.experimental.CoroutineDispatcher
import kotlinx.coroutines.experimental.Delay
import kotlinx.coroutines.experimental.Yield
import kotlinx.coroutines.experimental.swing.Swing.delay
import java.awt.event.ActionListener
import java.util.concurrent.TimeUnit
import javax.swing.SwingUtilities
import javax.swing.Timer
import kotlin.coroutines.CoroutineContext

/**
 * Dispatches execution onto Swing event dispatching thread and provides native [delay] support.
 */
object Swing : CoroutineDispatcher(), Yield, Delay {
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = !SwingUtilities.isEventDispatchThread()
    override fun dispatch(context: CoroutineContext, block: Runnable) = SwingUtilities.invokeLater(block)

    override fun scheduleResume(continuation: CancellableContinuation<Unit>) {
        SwingUtilities.invokeLater { continuation.resume(Unit) }
    }

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        val timerTime = unit.toMillis(time).coerceAtMost(Int.MAX_VALUE.toLong()).toInt()
        val timer = Timer(timerTime, ActionListener { continuation.resume(Unit) }).apply {
            isRepeats = false
            start()
        }
        continuation.onCompletion { timer.stop() }
    }
}
