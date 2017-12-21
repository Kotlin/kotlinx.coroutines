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

import kotlinx.coroutines.experimental.channels.Channel
import kotlinx.coroutines.experimental.selects.select
import kotlinx.coroutines.experimental.sync.Mutex
import kotlin.test.*

class AtomicCancellationTest : TestBase() {
    @Test
    fun testLockAtomicCancel() = runBlocking {
        expect(1)
        val mutex = Mutex(true) // locked mutex
        val job = launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            mutex.lock() // suspends
            expect(4) // should execute despite cancellation
        }
        expect(3)
        mutex.unlock() // unlock mutex first
        job.cancel() // cancel the job next
        yield() // now yield
        finish(5)
    }

    @Test
    fun testSelectLockAtomicCancel() = runBlocking {
        expect(1)
        val mutex = Mutex(true) // locked mutex
        val job = launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val result = select<String> { // suspends
                mutex.onLock {
                    expect(4)
                    "OK"
                }
            }
            assertEquals("OK", result)
            expect(5) // should execute despite cancellation
        }
        expect(3)
        mutex.unlock() // unlock mutex first
        job.cancel() // cancel the job next
        yield() // now yield
        finish(6)
    }

    @Test
    fun testSendAtomicCancel() = runBlocking {
        expect(1)
        val channel = Channel<Int>()
        val job = launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            channel.send(42) // suspends
            expect(4) // should execute despite cancellation
        }
        expect(3)
        assertEquals(42, channel.receive()) // will schedule sender for further execution
        job.cancel() // cancel the job next
        yield() // now yield
        finish(5)
    }

    @Test
    fun testSelectSendAtomicCancel() = runBlocking {
        expect(1)
        val channel = Channel<Int>()
        val job = launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val result = select<String> { // suspends
                channel.onSend(42) {
                    expect(4)
                    "OK"
                }
            }
            assertEquals("OK", result)
            expect(5) // should execute despite cancellation
        }
        expect(3)
        assertEquals(42, channel.receive()) // will schedule sender for further execution
        job.cancel() // cancel the job next
        yield() // now yield
        finish(6)
    }

    @Test
    fun testReceiveAtomicCancel() = runBlocking {
        expect(1)
        val channel = Channel<Int>()
        val job = launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            assertEquals(42, channel.receive()) // suspends
            expect(4) // should execute despite cancellation
        }
        expect(3)
        channel.send(42) // will schedule receiver for further execution
        job.cancel() // cancel the job next
        yield() // now yield
        finish(5)
    }

    @Test
    fun testSelectReceiveAtomicCancel() = runBlocking {
        expect(1)
        val channel = Channel<Int>()
        val job = launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val result = select<String> { // suspends
                channel.onReceive {
                    assertEquals(42, it)
                    expect(4)
                    "OK"
                }
            }
            assertEquals("OK", result)
            expect(5) // should execute despite cancellation
        }
        expect(3)
        channel.send(42) // will schedule receiver for further execution
        job.cancel() // cancel the job next
        yield() // now yield
        finish(6)
    }

    @Test
    fun testSelectDeferredAwaitCancellable() = runBlocking {
        expect(1)
        val deferred = async(coroutineContext) { // deferred, not yet complete
            expect(4)
            "OK"
        }
        assertEquals(false, deferred.isCompleted)
        var job: Job? = null
        launch(coroutineContext) { // will cancel job as soon as deferred completes
            expect(5)
            assertEquals(true, deferred.isCompleted)
            job!!.cancel()
        }
        job = launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
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
        expect(3) // continues to execute when job suspends
        yield() // to deferred & canceller
        expect(6)
    }

    @Test
    fun testSelectJobJoinCancellable() = runBlocking {
        expect(1)
        val jobToJoin = launch(coroutineContext) { // not yet complete
            expect(4)
        }
        assertEquals(false, jobToJoin.isCompleted)
        var job: Job? = null
        launch(coroutineContext) { // will cancel job as soon as jobToJoin completes
            expect(5)
            assertEquals(true, jobToJoin.isCompleted)
            job!!.cancel()
        }
        job = launch(coroutineContext, start = CoroutineStart.UNDISPATCHED) {
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
        expect(3) // continues to execute when job suspends
        yield() // to jobToJoin & canceller
        expect(6)
    }
}