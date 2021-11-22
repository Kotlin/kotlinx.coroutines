/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.javafx

import javafx.animation.*
import javafx.application.*
import javafx.event.*
import javafx.util.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.lang.UnsupportedOperationException
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
    override fun dispatch(context: CoroutineContext, block: Runnable): Unit = Platform.runLater(block)

    /** @suppress */
    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val timeline = schedule(timeMillis, TimeUnit.MILLISECONDS) {
            with(continuation) { resumeUndispatched(Unit) }
        }
        continuation.invokeOnCancellation { timeline.stop() }
    }

    /** @suppress */
    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        val timeline = schedule(timeMillis, TimeUnit.MILLISECONDS) {
            block.run()
        }
        return DisposableHandle { timeline.stop() }
    }

    private fun schedule(time: Long, unit: TimeUnit, handler: EventHandler<ActionEvent>): Timeline =
        Timeline(KeyFrame(Duration.millis(unit.toMillis(time).toDouble()), handler)).apply { play() }
}

internal class JavaFxDispatcherFactory : MainDispatcherFactory {
    override fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher = JavaFx

    override val loadPriority: Int
        get() = 1 // Swing has 0
}

private object ImmediateJavaFxDispatcher : JavaFxDispatcher() {
    override val immediate: MainCoroutineDispatcher
        get() = this

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = !Platform.isFxApplicationThread()

    override fun toString() = toStringInternalImpl() ?: "JavaFx.immediate"
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

    override fun toString() = toStringInternalImpl() ?: "JavaFx"
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

/** @return true if initialized successfully, and false if no display is detected */
internal fun initPlatform(): Boolean = PlatformInitializer.success

// Lazily try to initialize JavaFx platform just once
private object PlatformInitializer {
    val success = run {
        /*
         * Try to instantiate JavaFx platform in a way which works
         * both on Java 8 and Java 11 and does not produce "illegal reflective access".
         */
        try {
            val runnable = Runnable {}
            // Invoke the public API if it is present.
            runCatching {
                Class.forName("javafx.application.Platform")
                        .getMethod("startup", java.lang.Runnable::class.java)
            }.map { method ->
                method.invoke(null, runnable)
                return@run true
            }
            // If we are here, it means the public API is not present. Try the private API.
            Class.forName("com.sun.javafx.application.PlatformImpl")
                    .getMethod("startup", java.lang.Runnable::class.java)
                    .invoke(null, runnable)
            true
        } catch (exception: InvocationTargetException) {
            // Can only happen as a result of [Method.invoke].
            val cause = exception.cause!!
            when {
                // Maybe the problem is that JavaFX is already initialized? Everything is good then.
                cause is IllegalStateException && "Toolkit already initialized" == cause.message -> true
                // If the problem is the headless environment, it is okay.
                cause is UnsupportedOperationException && "Unable to open DISPLAY" == cause.message -> false
                // Otherwise, the exception demonstrates an anomaly.
                else -> throw cause
            }
        }
    }
}
