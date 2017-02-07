/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

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
import kotlin.coroutines.experimental.CoroutineContext


/**
 * Dispatches execution onto JavaFx application thread and provides native [delay] support.
 */
object JavaFx : CoroutineDispatcher(), Delay {
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
