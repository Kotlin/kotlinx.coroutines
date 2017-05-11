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
import org.hamcrest.core.IsEqual
import org.junit.Assert.assertThat
import org.junit.Test

class AtomicCancellationTest: TestBase() {
    @Test
    fun testCancellableLaunch() = runBlocking {
        expect(1)
        val job = launch(context) {
            expectUnreached() // will get cancelled before start
        }
        expect(2)
        job.cancel()
        finish(3)
    }

    @Test
    fun testAtomicLaunch() = runBlocking {
        expect(1)
        val job = launch(context, start = CoroutineStart.ATOMIC) {
            finish(4) // will execute even after it was cancelled
        }
        expect(2)
        job.cancel()
        expect(3)
    }

    @Test
    fun testLockAtomicCancel() = runBlocking {
        expect(1)
        val mutex = Mutex(true) // locked mutex
        val job = launch(context, start = CoroutineStart.UNDISPATCHED) {
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
        val job = launch(context, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val result = select<String> { // suspends
                mutex.onLock {
                    expect(4)
                    "OK"
                }
            }
            assertThat(result, IsEqual("OK"))
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
        val job = launch(context, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            channel.send(42) // suspends
            expect(4) // should execute despite cancellation
        }
        expect(3)
        assertThat(channel.receive(), IsEqual(42)) // will schedule sender for further execution
        job.cancel() // cancel the job next
        yield() // now yield
        finish(5)
    }

    @Test
    fun testSelectSendAtomicCancel() = runBlocking {
        expect(1)
        val channel = Channel<Int>()
        val job = launch(context, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val result = select<String> { // suspends
                channel.onSend(42) {
                    expect(4)
                    "OK"
                }
            }
            assertThat(result, IsEqual("OK"))
            expect(5) // should execute despite cancellation
        }
        expect(3)
        assertThat(channel.receive(), IsEqual(42)) // will schedule sender for further execution
        job.cancel() // cancel the job next
        yield() // now yield
        finish(6)
    }

    @Test
    fun testReceiveAtomicCancel() = runBlocking {
        expect(1)
        val channel = Channel<Int>()
        val job = launch(context, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            assertThat(channel.receive(), IsEqual(42)) // suspends
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
        val job = launch(context, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            val result = select<String> { // suspends
                channel.onReceive {
                    assertThat(it, IsEqual(42))
                    expect(4)
                    "OK"
                }
            }
            assertThat(result, IsEqual("OK"))
            expect(5) // should execute despite cancellation
        }
        expect(3)
        channel.send(42) // will schedule receiver for further execution
        job.cancel() // cancel the job next
        yield() // now yield
        finish(6)
    }

    @Test
    fun testDeferredAwaitCancellable() = runBlocking {
        expect(1)
        val deferred = async(context) { // deferred, not yet complete
            expect(4)
            "OK"
        }
        assertThat(deferred.isCompleted, IsEqual(false))
        var job: Job? = null
        launch(context) { // will cancel job as soon as deferred completes
            expect(5)
            assertThat(deferred.isCompleted, IsEqual(true))
            job!!.cancel()
        }
        job = launch(context, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                deferred.await() // suspends
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
    fun testSelectDeferredAwaitCancellable() = runBlocking {
        expect(1)
        val deferred = async(context) { // deferred, not yet complete
            expect(4)
            "OK"
        }
        assertThat(deferred.isCompleted, IsEqual(false))
        var job: Job? = null
        launch(context) { // will cancel job as soon as deferred completes
            expect(5)
            assertThat(deferred.isCompleted, IsEqual(true))
            job!!.cancel()
        }
        job = launch(context, start = CoroutineStart.UNDISPATCHED) {
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
    fun testJobJoinCancellable() = runBlocking {
        expect(1)
        val jobToJoin = launch(context) { // not yet complete
            expect(4)
        }
        assertThat(jobToJoin.isCompleted, IsEqual(false))
        var job: Job? = null
        launch(context) { // will cancel job as soon as jobToJoin completes
            expect(5)
            assertThat(jobToJoin.isCompleted, IsEqual(true))
            job!!.cancel()
        }
        job = launch(context, start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                jobToJoin.join() // suspends
                expectUnreached() // will not execute -- cancelled while dispatched
            } finally {
                finish(7) // but will execute finally blocks
            }
        }
        expect(3) // continues to execute when job suspends
        yield() // to jobToJoin & canceller
        expect(6)
    }

    @Test
    fun testSelectJobJoinCancellable() = runBlocking {
        expect(1)
        val jobToJoin = launch(context) { // not yet complete
            expect(4)
        }
        assertThat(jobToJoin.isCompleted, IsEqual(false))
        var job: Job? = null
        launch(context) { // will cancel job as soon as jobToJoin completes
            expect(5)
            assertThat(jobToJoin.isCompleted, IsEqual(true))
            job!!.cancel()
        }
        job = launch(context, start = CoroutineStart.UNDISPATCHED) {
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