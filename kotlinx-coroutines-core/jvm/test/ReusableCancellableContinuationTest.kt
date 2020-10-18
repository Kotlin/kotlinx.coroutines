/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class ReusableCancellableContinuationTest : TestBase() {

    @Test
    fun testReusable() = runTest {
        testContinuationsCount(10, 1, ::suspendAtomicCancellableCoroutineReusable)
    }

    @Test
    fun testRegular() = runTest {
        testContinuationsCount(10, 10, ::suspendAtomicCancellableCoroutine)
    }

    private suspend inline fun CoroutineScope.testContinuationsCount(
        iterations: Int,
        expectedInstances: Int,
        suspender: suspend ((CancellableContinuation<Unit>) -> Unit) -> Unit
    ) {
        val result = mutableSetOf<CancellableContinuation<*>>()
        val job = coroutineContext[Job]!!
        val channel = Channel<Continuation<Unit>>(1)
        launch {
            channel.consumeEach {
                val f = FieldWalker.walk(job)
                result.addAll(f.filterIsInstance<CancellableContinuation<*>>())
                it.resumeWith(Result.success(Unit))
            }
        }

        repeat(iterations) {
            suspender {
                assertTrue(channel.offer(it))
            }
        }
        channel.close()
        assertEquals(expectedInstances, result.size - 1)
    }

    @Test
    fun testCancelledOnClaimedCancel() = runTest {
        expect(1)
        try {
            suspendAtomicCancellableCoroutineReusable<Unit> {
                it.cancel()
            }
            expectUnreached()
        } catch (e: CancellationException) {
            finish(2)
        }
    }

    @Test
    fun testNotCancelledOnClaimedResume() = runTest({ it is CancellationException }) {
        expect(1)
        // Bind child at first
        var continuation: Continuation<*>? = null
        suspendAtomicCancellableCoroutineReusable<Unit> {
            expect(2)
            continuation = it
            launch {  // Attach to the parent, avoid fast path
                expect(3)
                it.resume(Unit)
            }
        }
        expect(4)
        ensureActive()
        // Verify child was bound
        FieldWalker.assertReachableCount(1, coroutineContext[Job]) { it === continuation }
        suspendAtomicCancellableCoroutineReusable<Unit> {
            expect(5)
            coroutineContext[Job]!!.cancel()
            it.resume(Unit)
        }
        assertFalse(isActive)
        finish(6)
    }

    @Test
    fun testResumeReusablePreservesReference() = runTest {
        expect(1)
        var cont: Continuation<Unit>? = null
        launch {
            cont!!.resumeWith(Result.success(Unit))
        }
        suspendAtomicCancellableCoroutineReusable<Unit> {
            cont = it
        }
        ensureActive()
        assertTrue { FieldWalker.walk(coroutineContext[Job]).contains(cont!!) }
        finish(2)
    }

    @Test
    fun testResumeRegularDoesntPreservesReference() = runTest {
        expect(1)
        var cont: Continuation<Unit>? = null
        launch { // Attach to the parent, avoid fast path
            cont!!.resumeWith(Result.success(Unit))
        }
        suspendAtomicCancellableCoroutine<Unit> {
            cont = it
        }
        ensureActive()
        FieldWalker.assertReachableCount(0, coroutineContext[Job]) { it === cont }
        finish(2)
    }

    @Test
    fun testDetachedOnCancel() = runTest {
        expect(1)
        var cont: Continuation<*>? = null
        try {
            suspendAtomicCancellableCoroutineReusable<Unit> {
                cont = it
                it.cancel()
            }
            expectUnreached()
        } catch (e: CancellationException) {
            FieldWalker.assertReachableCount(0, coroutineContext[Job]) { it === cont }
            finish(2)
        }
    }

    @Test
    fun testPropagatedCancel() = runTest({it is CancellationException}) {
        val currentJob = coroutineContext[Job]!!
        expect(1)
        // Bind child at first
        suspendAtomicCancellableCoroutineReusable<Unit> {
            expect(2)
            // Attach to the parent, avoid fast path
            launch {
                expect(3)
                it.resume(Unit)
            }
        }
        expect(4)
        ensureActive()
        // Verify child was bound
        FieldWalker.assertReachableCount(1, currentJob) { it is CancellableContinuation<*> }
        currentJob.cancel()
        assertFalse(isActive)
        // Child detached
        FieldWalker.assertReachableCount(0, currentJob) { it is CancellableContinuation<*> }
        suspendAtomicCancellableCoroutineReusable<Unit> { it.resume(Unit) }
        suspendAtomicCancellableCoroutineReusable<Unit> { it.resume(Unit) }
        FieldWalker.assertReachableCount(0, currentJob) { it is CancellableContinuation<*> }

        try {
            suspendAtomicCancellableCoroutineReusable<Unit> {}
        } catch (e: CancellationException) {
            FieldWalker.assertReachableCount(0, currentJob) { it is CancellableContinuation<*> }
            finish(5)
        }
    }

    @Test
    fun testChannelMemoryLeak() = runTest {
        val iterations = 100
        val channel = Channel<Unit>()
        launch {
            repeat(iterations) {
                select {
                    channel.onSend(Unit) {}
                }
            }
        }

        val receiver = launch {
            repeat(iterations) {
                channel.receive()
            }
            expect(2)
            val job = coroutineContext[Job]!!
            // 1 for reusable CC, another one for outer joiner
            FieldWalker.assertReachableCount(2, job) { it is CancellableContinuation<*> }
        }
        expect(1)
        receiver.join()
        // Reference should be claimed at this point
        FieldWalker.assertReachableCount(0, receiver) { it is CancellableContinuation<*> }
        finish(3)
    }

    @Test
    fun testReusableAndRegularSuspendCancellableCoroutineMemoryLeak() = runTest {
        val channel =  produce {
            repeat(10) {
                send(Unit)
            }
        }
        for (value in channel) {
            delay(1)
        }
        FieldWalker.assertReachableCount(1, coroutineContext[Job]) { it is ChildContinuation }
    }
}
