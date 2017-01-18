package kotlinx.coroutines.experimental.javafx

import javafx.animation.AnimationTimer
import javafx.animation.KeyFrame
import javafx.animation.Timeline
import javafx.application.Platform
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.util.Duration
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.javafx.JavaFx.delay
import java.util.concurrent.CopyOnWriteArrayList
import java.util.concurrent.TimeUnit


/**
 * Dispatches execution onto JavaFx application thread and provides native [delay] support.
 */
object JavaFx : CoroutineDispatcher(), Delay {
    private val pulseTimer by lazy {
        PulseTimer().apply { start() }
    }

    override fun isDispatchNeeded(): Boolean = !Platform.isFxApplicationThread()
    override fun dispatch(block: Runnable) = Platform.runLater(block)

    /**
     * Suspends coroutine until next JavaFx pulse and returns time of the pulse on resumption.
     * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
     * immediately resumes with [CancellationException] .
     */
    suspend fun awaitPulse(): Long = suspendCancellableCoroutine { cont ->
        pulseTimer.onNext(cont)
    }

    override fun resumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        val timeline = Timeline(KeyFrame(Duration.millis(unit.toMillis(time).toDouble()),
                EventHandler<ActionEvent> { continuation.resume(Unit) }))
        timeline.play()
        continuation.onCompletion { timeline.stop() }
    }
}

private class PulseTimer : AnimationTimer() {
    val next = CopyOnWriteArrayList<CancellableContinuation<Long>>()

    override fun handle(now: Long) {
        val cur = next.toTypedArray()
        next.clear()
        for (cont in cur)
            cont.resume(now)
    }

    fun onNext(cont: CancellableContinuation<Long>) {
        next += cont
    }
}
