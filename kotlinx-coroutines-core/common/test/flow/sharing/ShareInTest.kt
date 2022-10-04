/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class ShareInTest : TestBase() {
    @Test
    fun testReplay0Eager() = runTest {
        expect(1)
        val flow = flowOf("OK")
        val shared = flow.shareIn(this, SharingStarted.Eagerly)
        yield() // actually start sharing
        // all subscribers miss "OK"
        val jobs = List(10) {
            shared.onEach { expectUnreached() }.launchIn(this)
        }
        yield() // ensure nothing is collected
        jobs.forEach { it.cancel() }
        finish(2)
    }

    @Test
    fun testReplay0Lazy() = testReplayZeroOrOne(0)

    @Test
    fun testReplay1Lazy() = testReplayZeroOrOne(1)

    private fun testReplayZeroOrOne(replay: Int) = runTest {
        expect(1)
        val doneBarrier = Job()
        val flow = flow {
            expect(2)
            emit("OK")
            doneBarrier.join()
            emit("DONE")
        }
        val sharingJob = Job()
        val shared = flow.shareIn(this + sharingJob, started = SharingStarted.Lazily, replay = replay)
        yield() // should not start sharing
        // first subscriber gets "OK", other subscribers miss "OK"
        val n = 10
        val replayOfs = replay * (n - 1)
        val subscriberJobs = List(n) { index ->
            val subscribedBarrier = Job()
            val job = shared
                .onSubscription {
                    subscribedBarrier.complete()
                }
                .onEach { value ->
                    when (value) {
                        "OK" -> {
                            expect(3 + index)
                            if (replay == 0) { // only the first subscriber collects "OK" without replay
                                assertEquals(0, index)
                            }
                        }
                        "DONE" -> {
                            expect(4 + index + replayOfs)
                        }
                        else -> expectUnreached()
                    }
                }
                .takeWhile { it != "DONE" }
                .launchIn(this)
            subscribedBarrier.join() // wait until the launched job subscribed before launching the next one
            job
        }
        doneBarrier.complete()
        subscriberJobs.joinAll()
        expect(4 + n + replayOfs)
        sharingJob.cancel()
        finish(5 + n + replayOfs)
    }

    @Test
    fun testUpstreamCompleted() =
        testUpstreamCompletedOrFailed(failed = false)

    @Test
    fun testUpstreamFailed() =
        testUpstreamCompletedOrFailed(failed = true)

    private fun testUpstreamCompletedOrFailed(failed: Boolean) = runTest {
        val emitted = Job()
        val terminate = Job()
        val sharingJob = CompletableDeferred<Unit>()
        val upstream = flow {
            emit("OK")
            emitted.complete()
            terminate.join()
            if (failed) throw TestException()
        }
        val shared = upstream.shareIn(this + sharingJob, SharingStarted.Eagerly, 1)
        assertEquals(emptyList(), shared.replayCache)
        emitted.join() // should start sharing, emit & cache
        assertEquals(listOf("OK"), shared.replayCache)
        terminate.complete()
        sharingJob.complete(Unit)
        sharingJob.join() // should complete sharing
        assertEquals(listOf("OK"), shared.replayCache) // cache is still there
        if (failed) {
            assertTrue(sharingJob.getCompletionExceptionOrNull() is TestException)
        } else {
            assertNull(sharingJob.getCompletionExceptionOrNull())
        }
    }

    @Test
    fun testWhileSubscribedBasic() =
        testWhileSubscribed(1, SharingStarted.WhileSubscribed())

    @Test
    fun testWhileSubscribedCustomAtLeast1() =
        testWhileSubscribed(1, SharingStarted.WhileSubscribedAtLeast(1))

    @Test
    fun testWhileSubscribedCustomAtLeast2() =
        testWhileSubscribed(2, SharingStarted.WhileSubscribedAtLeast(2))

    @OptIn(ExperimentalStdlibApi::class)
    private fun testWhileSubscribed(threshold: Int, started: SharingStarted) = runTest {
        expect(1)
        val flowState = FlowState()
        val n = 3 // max number of subscribers
        val log = Channel<String>(2 * n)

        suspend fun checkStartTransition(subscribers: Int) {
            when (subscribers) {
                in 0 until threshold -> assertFalse(flowState.started)
                threshold -> {
                    flowState.awaitStart() // must eventually start the flow
                    for (i in 1..threshold) {
                        assertEquals("sub$i: OK", log.receive()) // threshold subs must receive the values
                    }
                }
                in threshold + 1..n -> assertTrue(flowState.started)
            }
        }

        suspend fun checkStopTransition(subscribers: Int) {
            when (subscribers) {
                in threshold + 1..n -> assertTrue(flowState.started)
                threshold - 1 -> flowState.awaitStop() // upstream flow must be eventually stopped
                in 0..threshold - 2 -> assertFalse(flowState.started) // should have stopped already
            }
        }

        val flow = flow {
            flowState.track {
                emit("OK")
                delay(Long.MAX_VALUE) // await forever, will get cancelled
            }
        }
        
        val shared = flow.shareIn(this, started)
        repeat(5) { // repeat scenario a few times
            yield()
            assertFalse(flowState.started) // flow is not running even if we yield
            // start 3 subscribers
            val subs = ArrayList<Job>()
            for (i in 1..n) {
                subs += shared
                    .onEach { value -> // only the first threshold subscribers get the value
                        when (i) {
                            in 1..threshold -> log.trySend("sub$i: $value")
                            else -> expectUnreached()
                        }
                    }
                    .onCompletion { log.trySend("sub$i: completion") }
                    .launchIn(this)
                checkStartTransition(i)
            }
            // now cancel all subscribers
            for (i in 1..n) {
                subs.removeFirst().cancel() // cancel subscriber
                assertEquals("sub$i: completion", log.receive()) // subscriber shall shutdown
                checkStopTransition(n - i)
            }
        }
        coroutineContext.cancelChildren() // cancel sharing job
        finish(2)
    }

    @Suppress("TestFunctionName")
    private fun SharingStarted.Companion.WhileSubscribedAtLeast(threshold: Int) =
        SharingStarted { subscriptionCount ->
            subscriptionCount.map { if (it >= threshold) SharingCommand.START else SharingCommand.STOP }
        }

    private class FlowState {
        private val timeLimit = 10000L
        private val _started = MutableStateFlow(false)
        val started: Boolean get() = _started.value
        fun start() = check(_started.compareAndSet(expect = false, update = true))
        fun stop() = check(_started.compareAndSet(expect = true, update = false))
        suspend fun awaitStart() = withTimeout(timeLimit) { _started.first { it } }
        suspend fun awaitStop() = withTimeout(timeLimit) { _started.first { !it } }
    }

    private suspend fun FlowState.track(block: suspend () -> Unit) {
        start()
        try {
            block()
        } finally {
            stop()
        }
    }

    @Test
    fun testShouldStart() = runTest {
        val flow = flow {
            expect(2)
            emit(1)
            expect(3)
        }.shareIn(this, SharingStarted.Lazily)

        expect(1)
        flow.onSubscription { throw CancellationException("") }
            .catch { e -> assertTrue { e is CancellationException } }
            .collect()
        yield()
        finish(4)
    }

    @Test
    fun testShouldStartScalar() = runTest {
        val j = Job()
        val shared = flowOf(239).stateIn(this + j, SharingStarted.Lazily, 42)
        assertEquals(42, shared.first())
        yield()
        assertEquals(239, shared.first())
        j.cancel()
    }
}
