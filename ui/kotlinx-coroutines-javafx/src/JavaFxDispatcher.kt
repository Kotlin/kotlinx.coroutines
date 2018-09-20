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
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

/**
 * Dispatches execution onto JavaFx application thread and provides native [delay] support.
 */
public val Dispatchers.JavaFx: JavaFxDispatcher
    get() = kotlinx.coroutines.experimental.javafx.JavaFx

/**
 * Dispatcher for JavaFx application thread with support for [awaitPulse].
 *
 * This class provides type-safety and a point for future extensions.
 */
public sealed class JavaFxDispatcher : CoroutineDispatcher(), Delay {
}

/**
 * Dispatches execution onto JavaFx application thread and provides native [delay] support.
 * @suppress **Deprecated**: Use [Dispatchers.JavaFx].
 */
@Deprecated(
    message = "Use Dispatchers.JavaFx",
    replaceWith = ReplaceWith("Dispatchers.JavaFx",
        imports = ["kotlinx.coroutines.experimental.Dispatchers", "kotlinx.coroutines.experimental.javafx.JavaFx"])
)
// todo: it will become an internal implementation object
object JavaFx : JavaFxDispatcher(), Delay {
    init {
        // :kludge: to make sure Toolkit is initialized if we use JavaFx dispatcher outside of JavaFx app
        initPlatform()
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) = Platform.runLater(block)

    /**
     * Suspends coroutine until next JavaFx pulse and returns time of the pulse on resumption.
     * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
     * immediately resumes with [CancellationException] .
     *
     * @suppress **Deprecated**: Use top-level [awaitPulse].
     */
    @Deprecated(
        message = "Use top-level awaitFrame",
        replaceWith = ReplaceWith("kotlinx.coroutines.experimental.javafx.awaitPulse()")
    )
    suspend fun awaitPulse(): Long =
        kotlinx.coroutines.experimental.javafx.awaitPulse()

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

    override fun toString() = "JavaFx"
}

private val pulseTimer by lazy {
    PulseTimer().apply { start() }
}

/**
 * Suspends coroutine until next JavaFx pulse and returns time of the pulse on resumption.
 * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException] .
 */
public suspend fun awaitPulse(): Long = suspendCancellableCoroutine { cont ->
    pulseTimer.onNext(cont)
}

private class PulseTimer : AnimationTimer() {
    val next = CopyOnWriteArrayList<CancellableContinuation<Long>>()

    override fun handle(now: Long) {
        val cur = next.toTypedArray()
        next.clear()
        for (cont in cur)
            with (cont) { JavaFx.resumeUndispatched(now) }
    }

    fun onNext(cont: CancellableContinuation<Long>) {
        next += cont
    }
}

internal fun initPlatform() {
    // Ad-hoc workaround for #443. Will be fixed with multi-release jar.
    // If this code throws an exception (Java 9 + prohibited reflective access), initialize JavaFX directly
    Class.forName("com.sun.javafx.application.PlatformImpl")
        .getMethod("startup", java.lang.Runnable::class.java)
        .invoke(null, java.lang.Runnable { })
}
