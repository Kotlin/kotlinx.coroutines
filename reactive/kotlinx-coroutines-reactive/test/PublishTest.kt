/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import org.reactivestreams.*

class PublishTest : TestBase() {
    @Test
    fun testBasicEmpty() = runTest {
        expect(1)
        val publisher = publish<Int> {
            expect(5)
        }
        expect(2)
        publisher.subscribe(object : Subscriber<Int> {
            override fun onSubscribe(s: Subscription?) { expect(3) }
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
        val publisher = publish {
            expect(5)
            send(42)
            expect(7)
        }
        expect(2)
        publisher.subscribe(object : Subscriber<Int> {
            override fun onSubscribe(s: Subscription) {
                expect(3)
                s.request(1)
            }
            override fun onNext(t: Int) {
                expect(6)
                assertThat(t, IsEqual(42))
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
        val publisher = publish<Int>(NonCancellable) {
            expect(5)
            throw RuntimeException("OK")
        }
        expect(2)
        publisher.subscribe(object : Subscriber<Int> {
            override fun onSubscribe(s: Subscription) {
                expect(3)
                s.request(1)
            }
            override fun onNext(t: Int) { expectUnreached() }
            override fun onComplete() { expectUnreached() }
            override fun onError(t: Throwable) {
                expect(6)
                assertThat(t, IsInstanceOf(RuntimeException::class.java))
                assertThat(t.message, IsEqual("OK"))
            }
        })
        expect(4)
        yield() // to publish coroutine
        finish(7)
    }

    @Test
    fun testCancelsParentOnFailure() = runTest(
        expected = { it is RuntimeException && it.message == "OK" }
    ) {
        // has parent, so should cancel it on failure
        publish<Unit> {
            throw RuntimeException("OK")
        }.openSubscription()
    }

    @Test
    fun testHandleFailureAfterCancel() = runTest(
        unhandled = listOf({ it -> it is RuntimeException && it.message == "FAILED" })
    ){
        expect(1)
        // Exception should be delivered to CoroutineExceptionHandler, because we create publisher
        // with the NonCancellable parent
        val publisher = publish<Unit>(NonCancellable + Dispatchers.Unconfined) {
            try {
                expect(3)
                delay(10000)
            } finally {
                expect(5)
                throw RuntimeException("FAILED") // crash after cancel
            }
        }
        var sub: Subscription? = null
        publisher.subscribe(object : Subscriber<Unit> {
            override fun onComplete() {
                expectUnreached()
            }

            override fun onSubscribe(s: Subscription) {
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
        finish(6)
    }

    @Test
    fun testPublishFailureCancelsParent() = runTest(
        expected = { it is TestException }
    ) {
        expect(1)
        val publisher = publish<Unit> {
            expect(5)
            throw TestException()
        }
        expect(2)
        publisher.subscribe(object : Subscriber<Unit> {
            override fun onComplete() {
                expectUnreached()
            }

            override fun onSubscribe(s: Subscription) {
                expect(3)
            }

            override fun onNext(t: Unit?) {
                expectUnreached()
            }

            override fun onError(t: Throwable?) {
                assertTrue(t is TestException)
                expect(6)
            }
        })
        expect(4)
        try {
            yield() // to coroutine, will crash because it is a cancelled parent coroutine
        } finally {
            finish(7)
        }
        expectUnreached()
    }

    @Test
    fun testOnNextError() = runTest {
        expect(1)
        val publisher = publish<String>(NonCancellable) {
            expect(4)
            try {
                send("OK")
            } catch(e: Throwable) {
                expect(6)
                assert(e is TestException)
            }
        }
        expect(2)
        val latch = CompletableDeferred<Unit>()
        publisher.subscribe(object : Subscriber<String> {
            override fun onComplete() {
                expectUnreached()
            }

            override fun onSubscribe(s: Subscription) {
                expect(3)
                s.request(1)
            }

            override fun onNext(t: String) {
                expect(5)
                assertEquals("OK", t)
                throw TestException()
            }

            override fun onError(t: Throwable) {
                expect(7)
                assert(t is TestException)
                latch.complete(Unit)
            }
        })
        latch.await()
        finish(8)
    }

    private class TestException : Exception()
}