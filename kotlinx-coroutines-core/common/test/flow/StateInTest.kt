/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class StateInTest : TestBase() {
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
}