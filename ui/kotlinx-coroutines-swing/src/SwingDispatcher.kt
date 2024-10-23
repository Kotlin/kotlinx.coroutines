package kotlinx.coroutines.swing

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.awt.event.*
import javax.swing.*
import kotlin.coroutines.*
import kotlin.time.Duration
import kotlin.time.DurationUnit

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
    override fun scheduleResumeAfterDelay(time: Duration, continuation: CancellableContinuation<Unit>) {
        val timer = schedule(time) {
            with(continuation) { resumeUndispatched(Unit) }
        }
        continuation.invokeOnCancellation { timer.stop() }
    }

    /** @suppress */
    override fun invokeOnTimeout(timeout: Duration, block: Runnable, context: CoroutineContext): DisposableHandle {
        val timer = schedule(timeout) {
            block.run()
        }
        return DisposableHandle { timer.stop() }
    }

    private fun schedule(time: Duration, action: ActionListener): Timer =
        Timer(time.toInt(DurationUnit.MILLISECONDS), action).apply {
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

    override fun toString() = toStringInternalImpl() ?: "Swing.immediate"
}

/**
 * Dispatches execution onto Swing event dispatching thread and provides native [delay] support.
 */
internal object Swing : SwingDispatcher() {

    /* A workaround so that the dispatcher's initialization crashes with an exception if running in a headless
    environment. This is needed so that this broken dispatcher is not used as the source of delays. */
    init {
        Timer(1) { }.apply {
            isRepeats = false
            start()
        }
    }

    override val immediate: MainCoroutineDispatcher
        get() = ImmediateSwingDispatcher

    override fun toString() = toStringInternalImpl() ?: "Swing"
}
