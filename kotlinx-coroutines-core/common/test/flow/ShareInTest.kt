/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class ShareInTest : TestBase() {
    @Test
    fun testZeroReplayEager() = runTest {
        expect(1)
        val flow = flowOf("OK")
        val shared = flow.shareIn(this, 0)
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
    fun testZeroReplayLazy() = testZeroOneReplay(0)

    @Test
    fun tesOneReplayLazy() = testZeroOneReplay(1)

    private fun testZeroOneReplay(replay: Int) = runTest {
        expect(1)
        val doneBarrier = Job()
        val flow = flow {
            expect(2)
            emit("OK")
            doneBarrier.join()
            emit("DONE")
        }
        val sharingJob = Job()
        val shared = flow.shareIn(this + sharingJob, replay, started = SharingStarted.Lazily)
        yield() // should not start sharing
        // first subscriber gets Ok, other subscribers miss "OK"
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
    fun testWhileSubscribedBasic() = runTest {
        expect(1)
        val flowState = FlowState()
        val log = Channel<String>(10)
        val flow = flow<String> {
            flowState.track {
                emit("OK")
                delay(Long.MAX_VALUE) // await forever
            }
        }
        val sharingJob = Job()
        val shared = flow.shareIn(this + sharingJob, 0, started = SharingStarted.WhileSubscribed)
        repeat(3) { // repeat chenario 3 times
            yield()
            assertFalse(flowState.started) // flow is not running even if we yield
            val sub1 = shared
                .onEach { value -> log.offer("sub1: $value") }
                .onCompletion { log.offer("sub1: completion") }
                .launchIn(this)
            flowState.awaitStart() // must eventually start the flow
            assertEquals("sub1: OK", log.receive()) // must receive the value
            val sub2 = shared
                .onEach { expectUnreached() }
                .onCompletion { log.offer("sub2: completion") }
                .launchIn(this)
            assertTrue(flowState.started) // flow is still running
            sub1.cancel() // cancel 1st subscriber
            assertEquals("sub1: completion", log.receive()) // must eventually complete
            assertTrue(flowState.started) // flow is still running
            sub2.cancel() // cancel 2nd subscriber
            assertEquals("sub2: completion", log.receive()) // must eventually complete
            flowState.awaitStop() // upstream flow must be eventually stopped
        }
        sharingJob.cancel() // cancel sharing job
        finish(2)
    }

    private class FlowState {
        private val _started = MutableStateFlow(false)
        val started: Boolean get() = _started.value
        fun start() = check(_started.compareAndSet(expect = false, update = true))
        fun stop() = check(_started.compareAndSet(expect = true, update = false))
        suspend fun awaitStart() = _started.first { it }
        suspend fun awaitStop() = _started.first { !it }
    }

    private suspend fun FlowState.track(block: suspend () -> Unit) {
        start()
        try {
            block()
        } finally {
            stop()
        }
    }
}