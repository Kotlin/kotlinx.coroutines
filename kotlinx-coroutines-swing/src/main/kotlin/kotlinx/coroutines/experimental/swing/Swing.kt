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

package kotlinx.coroutines.experimental.swing

import kotlinx.coroutines.experimental.CancellableContinuation
import kotlinx.coroutines.experimental.CoroutineDispatcher
import kotlinx.coroutines.experimental.Delay
import kotlinx.coroutines.experimental.swing.Swing.delay
import java.awt.event.ActionListener
import java.util.concurrent.TimeUnit
import javax.swing.SwingUtilities
import javax.swing.Timer
import kotlin.coroutines.experimental.CoroutineContext

/**
 * Dispatches execution onto Swing event dispatching thread and provides native [delay] support.
 */
object Swing : CoroutineDispatcher(), Delay {
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = !SwingUtilities.isEventDispatchThread()
    override fun dispatch(context: CoroutineContext, block: Runnable) = SwingUtilities.invokeLater(block)

    override fun scheduleResumeAfterDelay(time: Long, unit: TimeUnit, continuation: CancellableContinuation<Unit>) {
        val timerTime = unit.toMillis(time).coerceAtMost(Int.MAX_VALUE.toLong()).toInt()
        val timer = Timer(timerTime, ActionListener { continuation.resume(Unit) }).apply {
            isRepeats = false
            start()
        }
        continuation.onCompletion { timer.stop() }
    }
}
