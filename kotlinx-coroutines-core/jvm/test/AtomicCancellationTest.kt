/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
import kotlin.test.*

class AtomicCancellationTest : TestBase() {
    @Test
    fun testSendCancellable() = runBlocking {
        expect(1)
        val channel = Channel<Int>()
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            channel.send(42) // suspends
            expectUnreached() // should NOT execute because of cancellation
        }
        expect(3)
        assertEquals(42, channel.receive()) // will schedule sender for further execution
        job.cancel() // cancel the job next
        yield() // now yield
        finish(4)
    }

    @Test
    fun testSelectSendCancellable() = runBlocking {
        expect(1)
        val channel = Channel<Int>()
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val result = select<String> { // suspends
                channel.onSend(42) {
                    expect(4)
                    "OK"
                }
            }
            expectUnreached() // should NOT execute because of cancellation
        }
        expect(3)
        assertEquals(42, channel.receive()) // will schedule sender for further execution
        job.cancel() // cancel the job next
        yield() // now yield
        finish(4)
    }

    @Test
    fun testReceiveCancellable() = runBlocking {
        expect(1)
        val channel = Channel<Int>()
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            assertEquals(42, channel.receive()) // suspends
            expectUnreached() // should NOT execute because of cancellation
        }
        expect(3)
        channel.send(42) // will schedule receiver for further execution
        job.cancel() // cancel the job next
        yield() // now yield
        finish(4)
    }

    @Test
    fun testSelectReceiveCancellable() = runBlocking {
        expect(1)
        val channel = Channel<Int>()
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val result = select<String> { // suspends
                channel.onReceive {
                    assertEquals(42, it)
                    expect(4)
                    "OK"
                }
            }
            expectUnreached() // should NOT execute because of cancellation
        }
        expect(3)
        channel.send(42) // will schedule receiver for further execution
        job.cancel() // cancel the job next
        yield() // now yield
        finish(4)
    }

    @Test
    fun testSelectDeferredAwaitCancellable() = runBlocking {
        expect(1)
        val deferred = async { // deferred, not yet complete
            expect(4)
            "OK"
        }
        assertEquals(false, deferred.isCompleted)
        var job: Job? = null
        launch { // will cancel job as soon as deferred completes
            expect(5)
            assertEquals(true, deferred.isCompleted)
            job!!.cancel()
        }
        job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                select<Unit> { // suspends
                    deferred.onAwait { expectUnreached() }
                }
                expectUnreached() // will not execute -- cancelled while dispatched
            } finally {
                finish(7) // but will execute finally blocks
            }
        }
        expect(3) // continues to execute when the job suspends
        yield() // to deferred & canceller
        expect(6)
    }

    @Test
    fun testSelectJobJoinCancellable() = runBlocking {
        expect(1)
        val jobToJoin = launch { // not yet complete
            expect(4)
        }
        assertEquals(false, jobToJoin.isCompleted)
        var job: Job? = null
        launch { // will cancel job as soon as jobToJoin completes
            expect(5)
            assertEquals(true, jobToJoin.isCompleted)
            job!!.cancel()
        }
        job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                select<Unit> { // suspends
                    jobToJoin.onJoin { expectUnreached() }
                }
                expectUnreached() // will not execute -- cancelled while dispatched
            } finally {
                finish(7) // but will execute finally blocks
            }
        }
        expect(3) // continues to execute when the job suspends
        yield() // to jobToJoin & canceller
        expect(6)
    }
}