/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.javafx

import javafx.animation.*
import javafx.application.*
import javafx.event.*
import javafx.util.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.lang.IllegalStateException
import java.lang.reflect.*
import java.util.concurrent.*
import kotlin.coroutines.*

/**
 * Dispatches execution onto JavaFx application thread and provides native [delay] support.
 */
@Suppress("unused")
public val Dispatchers.JavaFx: JavaFxDispatcher
    get() = kotlinx.coroutines.javafx.JavaFx

/**
 * Dispatcher for JavaFx application thread with support for [awaitPulse].
 *
 * This class provides type-safety and a point for future extensions.
 */
public sealed class JavaFxDispatcher : MainCoroutineDispatcher(), Delay {

    /** @suppress */
    override fun dispatch(context: CoroutineContext, block: Runnable) = Platform.runLater(block)

    /** @suppress */
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val timeline = schedule(timeMillis, TimeUnit.MILLISECONDS, EventHandler {
            with(continuation) { resumeUndispatched(Unit) }
        })
        continuation.invokeOnCancellation { timeline.stop() }
    }

    /** @suppress */
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        val timeline = schedule(timeMillis, TimeUnit.MILLISECONDS, EventHandler {
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
}

internal class JavaFxDispatcherFactory : MainDispatcherFactory {
    override fun createDispatcher(): MainCoroutineDispatcher = JavaFx

    override val loadPriority: Int
        get() = 1 // Swing has 0
}

private object ImmediateJavaFxDispatcher : JavaFxDispatcher() {
    override val immediate: MainCoroutineDispatcher
        get() = this

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = !Platform.isFxApplicationThread()

    override fun toString() = "JavaFx [immediate]"
}

/**
 * Dispatches execution onto JavaFx application thread and provides native [delay] support.
 */
internal object JavaFx : JavaFxDispatcher() {
    init {
        // :kludge: to make sure Toolkit is initialized if we use JavaFx dispatcher outside of JavaFx app
        initPlatform()
    }

    override val immediate: MainCoroutineDispatcher
        get() = ImmediateJavaFxDispatcher

    override fun toString() = "JavaFx"
}

private val pulseTimer by lazy {
    PulseTimer().apply { start() }
}

/**
 * Suspends coroutine until next JavaFx pulse and returns time of the pulse on resumption.
 * If the [Job] of the current coroutine is completed while this suspending function is waiting, this function
 * immediately resumes with [CancellationException][kotlinx.coroutines.CancellationException].
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
    /*
     * Try to instantiate JavaFx platform in a way which works
     * both on Java 8 and Java 11 and does not produce "illegal reflective access":
     *
     * 1) Try to invoke javafx.application.Platform.startup if this class is
     *    present in a classpath (since Java 9 it is a separate dependency)
     * 2) If it is not present, invoke plain old PlatformImpl.startup
     *
     * Additionally, ignore ISE("Toolkit already initialized") because since Java 9
     * consecutive calls to 'startup' throw it
     */
    val platformClass = runCatching {
        Class.forName("javafx.application.Platform") // Java 9+
    }.getOrElse {
        Class.forName("com.sun.javafx.application.PlatformImpl") // Fallback
    }

    try {
        platformClass.getMethod("startup", java.lang.Runnable::class.java)
            .invoke(null, java.lang.Runnable { })
    } catch (e: InvocationTargetException) {
        val cause = e.cause
        if (cause !is IllegalStateException || "Toolkit already initialized" != cause.message) {
            throw e
        }
    }
}
