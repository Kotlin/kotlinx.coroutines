/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import org.junit.Test
import org.reactivestreams.*
import reactor.core.*
import reactor.core.publisher.*
import kotlin.concurrent.*
import kotlin.test.*

class MonoAwaitStressTest: TestBase() {
    private val N_REPEATS = 10_000 * stressTestMultiplier

    private var completed: Boolean = false

    private var thread: Thread? = null

    /**
     * Tests that [Mono.awaitSingleOrNull] does await [CoreSubscriber.onComplete] and does not return
     * the value as soon as it has it.
     */
    @Test
    fun testAwaitingRacingWithCompletion() = runTest {
        val mono = object: Mono<Int>() {
            override fun subscribe(s: CoreSubscriber<in Int>) {
                s.onSubscribe(object : Subscription {
                    override fun request(n: Long) {
                        thread = thread {
                            s.onNext(1)
                            Thread.yield()
                            completed = true
                            s.onComplete()
                        }
                    }

                    override fun cancel() {
                    }
                })
            }
        }
        repeat(N_REPEATS) {
            thread = null
            completed = false
            val value = mono.awaitSingleOrNull()
            assertTrue(completed, "iteration $it")
            assertEquals(1, value)
            thread!!.join()
        }
    }
}
