@file:OptIn(ExperimentalAtomicApi::class)

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.testing.*
import kotlin.concurrent.atomics.*
import kotlin.random.*
import kotlin.test.*
import kotlin.time.*

class SharingStressTest : TestBase() {
    private val testDuration = 1000L * stressTestMultiplier
    private val nSubscribers = 5
    private val testStarted = TimeSource.Monotonic.markNow()

    val emitterDispatcher = newSingleThreadContext("Emitter")

    val subscriberDispatcher = newFixedThreadPoolContext(nSubscribers, "Subscribers")

    @AfterTest
    fun tearDown() {
        subscriberDispatcher.close()
        emitterDispatcher.close()
    }

    @Test
    fun testNoReplayLazy() =
        testStress(0, started = SharingStarted.Lazily)

    @Test
    fun testNoReplayWhileSubscribed() =
        testStress(0, started = SharingStarted.WhileSubscribed())

    @Test
    fun testNoReplayWhileSubscribedTimeout() =
        testStress(0, started = SharingStarted.WhileSubscribed(stopTimeoutMillis = 50L))

    @Test
    fun testReplay100WhileSubscribed() =
        testStress(100, started = SharingStarted.WhileSubscribed())

    @Test
    fun testReplay100WhileSubscribedReset() =
        testStress(100, started = SharingStarted.WhileSubscribed(replayExpirationMillis = 0L))

    @Test
    fun testReplay100WhileSubscribedTimeout() =
        testStress(100, started = SharingStarted.WhileSubscribed(stopTimeoutMillis = 50L))

    @Test
    fun testStateLazy() =
        testStress(1, started = SharingStarted.Lazily)

    @Test
    fun testStateWhileSubscribed() =
        testStress(1, started = SharingStarted.WhileSubscribed())

    @Test
    fun testStateWhileSubscribedReset() =
        testStress(1, started = SharingStarted.WhileSubscribed(replayExpirationMillis = 0L))

    private fun testStress(replay: Int, started: SharingStarted) = runTest {
        log("-- Stress with replay=$replay, started=$started")
        val random = Random(1)
        val emitIndex = AtomicLong(0)
        val cancelledEmits = HashSet<Long>()
        val missingCollects = ConcurrentSynchronizedSet()
        // at most one copy of upstream can be running at any time
        val isRunning = AtomicInt(0)
        val upstream = flow {
            assertEquals(0, isRunning.fetchAndIncrement())
            try {
                while (true) {
                    val value = emitIndex.fetchAndIncrement()
                    try {
                        emit(value)
                    } catch (e: CancellationException) {
                        // emission was cancelled -> could be missing
                        cancelledEmits.add(value)
                        throw e
                    }
                }
            } finally {
                assertEquals(1, isRunning.fetchAndDecrement())
            }
        }
        val subCount = MutableStateFlow(0)
        val sharingJob = Job()
        val sharingScope = this + emitterDispatcher + sharingJob
        val usingStateFlow = replay == 1
        val sharedFlow = if (usingStateFlow) {
            upstream.stateIn(sharingScope, started, 0L)
        } else {
            upstream.shareIn(sharingScope, started, replay)
        }
        try {
            val subscribers = ArrayList<SubJob>()
            withTimeoutOrNull(testDuration) {
                // start and stop subscribers
                while (true) {
                    log("Staring $nSubscribers subscribers")
                    repeat(nSubscribers) {
                        subscribers += launchSubscriber(sharedFlow, usingStateFlow, subCount, missingCollects)
                    }
                    // wait until they all subscribed
                    subCount.first { it == nSubscribers }
                    // let them work a bit more & make sure emitter did not hang
                    val fromEmitIndex = emitIndex.load()
                    val waitEmitIndex = fromEmitIndex + 100 // wait until 100 emitted
                    withTimeout(10000) { // wait for at most 10s for something to be emitted
                        do {
                            delay(random.nextLong(50L..100L))
                        } while (emitIndex.load() < waitEmitIndex)  // Ok, enough was emitted, wait more if not
                    }
                    // Stop all subscribers and ensure they collected something
                    log("Stopping subscribers (emitted = ${emitIndex.load() - fromEmitIndex})")
                    subscribers.forEach {
                        it.job.cancelAndJoin()
                        assertTrue { it.count > 0 } // something must be collected too
                    }
                    subscribers.clear()
                    log("Intermission")
                    delay(random.nextLong(10L..100L)) // wait a bit before starting them again
                }
            }
            if (!subscribers.isEmpty()) {
                log("Stopping subscribers")
                subscribers.forEach { it.job.cancelAndJoin() }
            }
        } finally {
            log("--- Finally: Cancelling sharing job")
            sharingJob.cancel()
        }
        sharingJob.join() // make sure sharing job did not hang
        log("Emitter was cancelled ${cancelledEmits.size} times")
        log("Collectors missed ${missingCollects.size()} values")
        val missingCollectsSnapshot = missingCollects.snapshot()
        for (value in missingCollectsSnapshot) {
            assertTrue(value in cancelledEmits, "Value $value is missing for no apparent reason")
        }
    }

    private fun CoroutineScope.launchSubscriber(
        sharedFlow: SharedFlow<Long>,
        usingStateFlow: Boolean,
        subCount: MutableStateFlow<Int>,
        missingCollects: ConcurrentSynchronizedSet
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
                        else {
                            if (expected != j) {
                                if (j == expected + 1) {
                                    // if missing just one -- could be race with cancelled emit
                                    runBlocking {
                                        missingCollects.add(expected)
                                    }
                                } else {
                                    // broken otherwise
                                    assertEquals(expected, j)
                                }
                            }
                        }
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

    private fun log(msg: String) = println("${testStarted.elapsedNow().inWholeMilliseconds} ms: $msg")

    private fun MutableStateFlow<Int>.increment(delta: Int) {
        update { it + delta }
    }
}
