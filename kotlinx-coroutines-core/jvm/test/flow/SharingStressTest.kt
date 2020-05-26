/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.atomic.*
import kotlin.random.*
import kotlin.test.*

class SharingStressTest : TestBase() {
    private val testDuration = 1000L * stressTestMultiplier
    private val nSubscribers = 5

    @get:Rule
    val emitterDispatcher = ExecutorRule(1)
    
    @get:Rule
    val subscriberDispatcher = ExecutorRule(nSubscribers)

    @Test
    public fun testNoReplayLazy() = testStress(0, started = SharingStarted.Lazily)

    @Test
    public fun testNoReplayWhileSubscribed() = testStress(0, started = SharingStarted.WhileSubscribed)

    @Test
    public fun testNoReplayWhileSubscribedTimeout() = testStress(0, started = SharingStarted.WhileSubscribed(stopTimeoutMillis = 50L))

    @Test
    public fun testReplay100WhileSubscribed() = testStress(100, started = SharingStarted.WhileSubscribed)

    @Test
    public fun testReplay100WhileSubscribedTimeout() = testStress(100, started = SharingStarted.WhileSubscribed(stopTimeoutMillis = 50L))

    @Test
    public fun testStateLazy() = testStress(1, started = SharingStarted.Lazily)

    @Test
    public fun testStateWhileSubscribed() = testStress(1, started = SharingStarted.WhileSubscribed)

    private fun testStress(replay: Int, started: SharingStarted) = runTest {
        val random = Random(1)
        val emitIndex = AtomicLong()
        // at most one copy of upstream can be running at any time
        val isRunning = AtomicInteger(0)
        val upstream = flow {
            assertEquals(0, isRunning.getAndIncrement())
            try {
                while (true) {
                    emit(emitIndex.getAndIncrement())
                }
            } finally {
                assertEquals(1, isRunning.getAndDecrement())
            }
        }
        val subCount = MutableStateFlow<Int>(0)
        val sharingJob = Job()
        val sharingScope = this + emitterDispatcher + sharingJob
        val usingStateFlow = replay == 1
        val sharedFlow = if (usingStateFlow)
            upstream.stateIn(sharingScope, started, 0L)
        else
            upstream.shareIn(sharingScope, replay, started)
        try {
            val subscribers = ArrayList<SubJob>()
            withTimeoutOrNull(testDuration) {
                // start and stop subscribers
                while (true) {
                    println("Staring $nSubscribers subscribers")
                    repeat(nSubscribers) {
                        subscribers += launchSubscriber(sharedFlow, usingStateFlow, subCount)
                    }
                    // wait until they all subscribed
                    subCount.first { it == nSubscribers }
                    // let them work a bit more
                    val fromEmitIndex = emitIndex.get()
                    for (attempt in 1..3) {
                        delay(random.nextLong(50L..100L))
                        if (emitIndex.get() > fromEmitIndex) break // Ok, something was emitted, wait more if not
                    }
                    val emitted = emitIndex.get() - fromEmitIndex
                    println("Stopping subscribers (emitted = $emitted)")
                    assertTrue(emitted > 0)
                    subscribers.forEach {
                        it.job.cancelAndJoin()
                        assertTrue { it.count > 0 } // something must be collected, too
                    }
                    subscribers.clear()
                    println("Intermission")
                    delay(random.nextLong(10L..100L)) // wait a bit before starting them again
                }
            }
            if (!subscribers.isEmpty()) {
                println("Stopping subscribers")
                subscribers.forEach { it.job.cancelAndJoin() }
            }
        } finally {
            println("Cancelling sharing job")
            sharingJob.cancel()
        }
    }

    private fun CoroutineScope.launchSubscriber(
        sharedFlow: SharedFlow<Long>,
        usingStateFlow: Boolean,
        subCount: MutableStateFlow<Int>
    ): SubJob {
        val subJob = SubJob()
        subJob.job = launch(subscriberDispatcher) {
            var last = -1L
            sharedFlow
                .onSubscription {
                    subCount.increment(1)
                }
                .onCompletion {
                    subCount.increment(-1)
                }
                .collect { j ->
                    subJob.count++
                    // last must grow sequentially, no jumping or losses
                    if (last == -1L) {
                        last = j
                    } else {
                        val expected = last + 1
                        if (usingStateFlow)
                            assertTrue(expected <= j)
                        else
                            assertEquals(expected, j)
                        last = j
                    }
                }
        }
        return subJob
    }

    private class SubJob {
        lateinit var job: Job
        var count = 0L
    }
}