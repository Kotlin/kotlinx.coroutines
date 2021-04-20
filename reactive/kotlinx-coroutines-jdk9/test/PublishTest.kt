/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.jdk9

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.Test
import java.util.concurrent.Flow as JFlow
import kotlin.test.*

class PublishTest : TestBase() {
    @Test
    fun testBasicEmpty() = runTest {
        expect(1)
        val publisher = flowPublish<Int>(currentDispatcher()) {
            expect(5)
        }
        expect(2)
        publisher.subscribe(object : JFlow.Subscriber<Int> {
            override fun onSubscribe(s: JFlow.Subscription?) { expect(3) }
            override fun onNext(t: Int?) { expectUnreached() }
            override fun onComplete() { expect(6) }
            override fun onError(t: Throwable?) { expectUnreached() }
        })
        expect(4)
        yield() // to publish coroutine
        finish(7)
    }

    @Test
    fun testBasicSingle() = runTest {
        expect(1)
        val publisher = flowPublish(currentDispatcher()) {
            expect(5)
            send(42)
            expect(7)
        }
        expect(2)
        publisher.subscribe(object : JFlow.Subscriber<Int> {
            override fun onSubscribe(s: JFlow.Subscription) {
                expect(3)
                s.request(1)
            }
            override fun onNext(t: Int) {
                expect(6)
                assertEquals(42, t)
            }
            override fun onComplete() { expect(8) }
            override fun onError(t: Throwable?) { expectUnreached() }
        })
        expect(4)
        yield() // to publish coroutine
        finish(9)
    }

    @Test
    fun testBasicError() = runTest {
        expect(1)
        val publisher = flowPublish<Int>(currentDispatcher()) {
            expect(5)
            throw RuntimeException("OK")
        }
        expect(2)
        publisher.subscribe(object : JFlow.Subscriber<Int> {
            override fun onSubscribe(s: JFlow.Subscription) {
                expect(3)
                s.request(1)
            }
            override fun onNext(t: Int) { expectUnreached() }
            override fun onComplete() { expectUnreached() }
            override fun onError(t: Throwable) {
                expect(6)
                assertTrue(t is RuntimeException)
                assertEquals("OK", t.message)
            }
        })
        expect(4)
        yield() // to publish coroutine
        finish(7)
    }

    @Test
    fun testHandleFailureAfterCancel() = runTest {
        expect(1)

        val eh = CoroutineExceptionHandler { _, t ->
            assertTrue(t is RuntimeException)
            expect(6)
        }
        val publisher = flowPublish<Unit>(Dispatchers.Unconfined + eh) {
            try {
                expect(3)
                delay(10000)
            } finally {
                expect(5)
                throw RuntimeException("FAILED") // crash after cancel
            }
        }
        var sub: JFlow.Subscription? = null
        publisher.subscribe(object : JFlow.Subscriber<Unit> {
            override fun onComplete() {
                expectUnreached()
            }

            override fun onSubscribe(s: JFlow.Subscription) {
                expect(2)
                sub = s
            }

            override fun onNext(t: Unit?) {
                expectUnreached()
            }

            override fun onError(t: Throwable?) {
                expectUnreached()
            }
        })
        expect(4)
        sub!!.cancel()
        finish(7)
    }

    /** Tests that, as soon as `ProducerScope.close` is called, `isClosedForSend` starts returning `true`. */
    @Test
    fun testChannelClosing() = runTest {
        expect(1)
        val publisher = flowPublish<Int>(Dispatchers.Unconfined) {
            expect(3)
            close()
            assert(isClosedForSend)
            expect(4)
        }
        try {
            expect(2)
            publisher.awaitFirstOrNull()
        } catch (e: CancellationException) {
            expect(5)
        }
        finish(6)
    }

    @Test
    fun testOnNextError() = runTest {
        val latch = CompletableDeferred<Unit>()
        expect(1)
        assertCallsExceptionHandlerWith<TestException> { exceptionHandler ->
            val publisher = flowPublish(currentDispatcher() + exceptionHandler) {
                expect(4)
                try {
                    send("OK")
                } catch (e: Throwable) {
                    expect(6)
                    assert(e is TestException)
                    assert(isClosedForSend)
                    latch.complete(Unit)
                }
            }
            expect(2)
            publisher.subscribe(object : JFlow.Subscriber<String> {
                override fun onComplete() {
                    expectUnreached()
                }

                override fun onSubscribe(s: JFlow.Subscription) {
                    expect(3)
                    s.request(1)
                }

                override fun onNext(t: String) {
                    expect(5)
                    assertEquals("OK", t)
                    throw TestException()
                }

                override fun onError(t: Throwable) {
                    expectUnreached()
                }
            })
            latch.await()
        }
        finish(7)
    }

    /** Tests the behavior when a call to `onNext` fails after the channel is already closed. */
    @Test
    fun testOnNextErrorAfterCancellation() = runTest {
        assertCallsExceptionHandlerWith<TestException> { handler ->
            var producerScope: ProducerScope<Int>? = null
            CompletableDeferred<Unit>()
            expect(1)
            var job: Job? = null
            val publisher = flowPublish<Int>(handler + Dispatchers.Unconfined) {
                producerScope = this
                expect(4)
                job = launch {
                    delay(Long.MAX_VALUE)
                }
            }
            expect(2)
            publisher.subscribe(object: JFlow.Subscriber<Int> {
                override fun onSubscribe(s: JFlow.Subscription) {
                    expect(3)
                    s.request(Long.MAX_VALUE)
                }
                override fun onNext(t: Int) {
                    expect(6)
                    assertEquals(1, t)
                    job!!.cancel()
                    throw TestException()
                }
                override fun onError(t: Throwable?) {
                    /* Correct changes to the implementation could lead to us entering or not entering this method, but
                    it only matters that if we do, it is the "correct" exception that was validly used to cancel the
                    coroutine that gets passed here and not `TestException`. */
                    assertTrue(t is CancellationException)
                }
                override fun onComplete() { expectUnreached() }
            })
            expect(5)
            val result: ChannelResult<Unit> = producerScope!!.trySend(1)
            val e = result.exceptionOrNull()!!
            assertTrue(e is CancellationException, "The actual error: $e")
            assertTrue(producerScope!!.isClosedForSend)
            assertTrue(result.isFailure)
        }
        finish(7)
    }

    @Test
    fun testFailingConsumer() = runTest {
        val pub = flowPublish(currentDispatcher()) {
            repeat(3) {
                expect(it + 1) // expect(1), expect(2) *should* be invoked
                send(it)
            }
        }
        try {
            pub.collect {
                throw TestException()
            }
        } catch (e: TestException) {
            finish(3)
        }
    }

    @Test
    fun testIllegalArgumentException() {
        assertFailsWith<IllegalArgumentException> { flowPublish<Int>(Job()) { } }
    }

    /** Tests that `trySend` doesn't throw in `flowPublish`. */
    @Test
    fun testTrySendNotThrowing() = runTest {
        var producerScope: ProducerScope<Int>? = null
        expect(1)
        val publisher = flowPublish<Int>(Dispatchers.Unconfined) {
            producerScope = this
            expect(3)
            delay(Long.MAX_VALUE)
        }
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            publisher.awaitFirstOrNull()
            expectUnreached()
        }
        job.cancel()
        expect(4)
        val result = producerScope!!.trySend(1)
        assertTrue(result.isFailure)
        finish(5)
    }

    /** Tests that all methods on `flowPublish` fail without closing the channel when attempting to emit `null`. */
    @Test
    fun testEmittingNull() = runTest {
        val publisher = flowPublish {
            assertFailsWith<NullPointerException> { send(null) }
            assertFailsWith<NullPointerException> { trySend(null) }
            @Suppress("DEPRECATION")
            assertFailsWith<NullPointerException> { offer(null) }
            send("OK")
        }
        assertEquals("OK", publisher.awaitFirstOrNull())
    }
}