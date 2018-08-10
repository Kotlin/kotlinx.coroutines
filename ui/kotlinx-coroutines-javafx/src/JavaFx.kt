/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.javafx

import javafx.animation.*
import javafx.application.*
import javafx.event.*
import javafx.util.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.javafx.JavaFx.delay
import java.util.concurrent.CopyOnWriteArrayList
import java.util.concurrent.TimeUnit
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Dispatches execution onto JavaFx application thread and provides native [delay] support.
 */
object JavaFx : CoroutineDispatcher(), Delay {
    init {
        // :kludge: to make sure Toolkit is initialized if we use JavaFx dispatcher outside of JavaFx app
        initPlatform()
    }

    private val pulseTimer by lazy {
        PulseTimer().apply { start() }
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) = Platform.runLater(block)

    /**
     * Suspends coroutine until next JavaFx pulse and returns time of the pulse on resumption.
     * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
     * immediately resumes with [CancellationException] .
     */
    suspend fun awaitPulse(): Long = suspendCancellableCoroutine { cont ->
        pulseTimer.onNext(cont)
    }

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        val timeline = schedule(time, unit, EventHandler {
            with(continuation) { resumeUndispatched(Unit) }
        })
        continuation.invokeOnCancellation { timeline.stop() }
    }

    override fun invokeOnTimeout(time: Long, unit: TimeUnit, block: Runnable): DisposableHandle {
        val timeline = schedule(time, unit, EventHandler {
            block.run()
        })
        return object : DisposableHandle {
            override fun dispose() {
                timeline.stop()
            }
        }
    }

    private fun schedule(time: Long, unit: TimeUnit, handler: EventHandler<ActionEvent>): Timeline =
        Timeline(KeyFrame(Duration.millis(unit.toMillis(time).toDouble()), handler)).apply { play() }

    private class PulseTimer : AnimationTimer() {
        val next = CopyOnWriteArrayList<CancellableContinuation<Long>>()

        override fun handle(now: Long) {
            val cur = next.toTypedArray()
            next.clear()
            for (cont in cur)
                with (cont) { resumeUndispatched(now) }
        }

        fun onNext(cont: CancellableContinuation<Long>) {
            next += cont
        }
    }

    override fun toString() = "JavaFx"
}

internal fun initPlatform() {
    // Ad-hoc workaround for #443. Will be fixed with multi-release jar.
    // If this code throws an exception (Java 9 + prohibited reflective access), initialize JavaFX directly
    Class.forName("com.sun.javafx.application.PlatformImpl")
        .getMethod("startup", java.lang.Runnable::class.java)
        .invoke(null, java.lang.Runnable { })
}
