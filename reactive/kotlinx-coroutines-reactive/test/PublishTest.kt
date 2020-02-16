/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactive

import kotlinx.coroutines.*
import org.junit.Test
import org.reactivestreams.*
import kotlin.test.*

class PublishTest : TestBase() {
    @Test
    fun testBasicEmpty() = runTest {
        expect(1)
        val publisher = publish<Int>(currentDispatcher()) {
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
        val publisher = publish(currentDispatcher()) {
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
        val publisher = publish<Int>(currentDispatcher()) {
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
        val publisher = publish<Unit>(Dispatchers.Unconfined + eh) {
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
        finish(7)
    }

    @Test
    fun testOnNextError() = runTest {
        expect(1)
        val publisher = publish(currentDispatcher()) {
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

    @Test
    fun testFailingConsumer() = runTest {
        val pub = publish(currentDispatcher()) {
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
        assertFailsWith<IllegalArgumentException> { publish<Int>(Job()) { } }
    }
}