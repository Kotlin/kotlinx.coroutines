/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactive

import kotlinx.coroutines.experimental.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import org.reactivestreams.*
import kotlin.coroutines.experimental.*

class PublishTest : TestBase() {
    @Test
    fun testBasicEmpty() = runBlocking<Unit> {
        expect(1)
        val publisher = publish<Int>(coroutineContext) {
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
    fun testBasicSingle() = runBlocking<Unit> {
        expect(1)
        val publisher = publish<Int>(coroutineContext) {
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
    fun testBasicError() = runBlocking<Unit> {
        expect(1)
        val publisher = publish<Int>(coroutineContext) {
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
}