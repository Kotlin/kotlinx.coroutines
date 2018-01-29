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

package kotlinx.coroutines.experimental

import kotlinx.atomicfu.*
import java.util.*
import java.util.concurrent.*
import kotlin.concurrent.*
import kotlin.test.*

class JobHandlersUpgradeStressTest : TestBase() {
    private val nSeconds = 3 * stressTestMultiplier
    private val nThreads = 4

    private val cyclicBarrier = CyclicBarrier(1 + nThreads)
    private val threads = mutableListOf<Thread>()

    private val inters = atomic(0)
    private val removed = atomic(0)
    private val fired = atomic(0)

    private val sink = atomic(0)

    @Volatile
    private var done = false

    @Volatile
    private var job: Job? = null

    class State {
        val state = atomic(0)
    }

    @Test
    fun testStress() {
        println("--- JobHandlersUpgradeStressTest")
        threads += thread(name = "creator", start = false) {
            val rnd = Random()
            while (true) {
                job = if (done) null else Job()
                cyclicBarrier.await()
                val job = job ?: break
                // burn some time
                repeat(rnd.nextInt(3000)) { sink.incrementAndGet() }
                // cancel job
                job.cancel()
                cyclicBarrier.await()
                inters.incrementAndGet()
            }
        }
        threads += List(nThreads) { threadId ->
            thread(name = "handler-$threadId", start = false) {
                val rnd = Random()
                while (true) {
                    val onCancelling = rnd.nextBoolean()
                    val invokeImmediately: Boolean = rnd.nextBoolean()
                    cyclicBarrier.await()
                    val job = job ?: break
                    val state = State()
                    // burn some time
                    repeat(rnd.nextInt(1000)) { sink.incrementAndGet() }
                    val handle =
                        job.invokeOnCompletion(onCancelling = onCancelling, invokeImmediately = invokeImmediately) {
                            if (!state.state.compareAndSet(0, 1))
                                error("Fired more than once or too late: state=${state.state.value}")
                        }
                    // burn some time
                    repeat(rnd.nextInt(1000)) { sink.incrementAndGet() }
                    // dispose
                    handle.dispose()
                    cyclicBarrier.await()
                    val resultingState = state.state.value
                    when (resultingState) {
                        0 -> removed.incrementAndGet()
                        1 -> fired.incrementAndGet()
                        else -> error("Cannot happen")
                    }
                    if (!state.state.compareAndSet(resultingState, 2))
                        error("Cannot fire late: resultingState=$resultingState")
                }
            }
        }
        threads.forEach { it.start() }
        repeat(nSeconds) { second ->
            Thread.sleep(1000)
            println("${second + 1}: ${inters.value} iterations")
        }
        done = true
        threads.forEach { it.join() }
        println("        Completed ${inters.value} iterations")
        println("  Removed handler ${removed.value} times")
        println("    Fired handler ${fired.value} times")

    }
}