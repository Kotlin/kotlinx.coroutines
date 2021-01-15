/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.*
import org.junit.Test
import org.reactivestreams.*
import reactor.core.publisher.*
import reactor.util.context.*
import java.time.*
import java.time.Duration.*
import java.util.function.*
import kotlin.test.*

class MonoTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("timer-", "parallel-")
    }

    @Test
    fun testBasicSuccess() = runBlocking {
        expect(1)
        val mono = mono(currentDispatcher()) {
            expect(4)
            "OK"
        }
        expect(2)
        mono.subscribe { value ->
            expect(5)
            assertEquals("OK", value)
        }
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicFailure() = runBlocking {
        expect(1)
        val mono = mono(currentDispatcher()) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        mono.subscribe({
            expectUnreached()
        }, { error ->
            expect(5)
            assertTrue(error is RuntimeException)
            assertEquals("OK", error.message)
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicEmpty() = runBlocking {
        expect(1)
        val mono = mono(currentDispatcher()) {
            expect(4)
            null
        }
        expect(2)
        mono.subscribe({}, { throw it }, {
            expect(5)
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicUnsubscribe() = runBlocking {
        expect(1)
        val mono = mono(currentDispatcher()) {
            expect(4)
            yield() // back to main, will get cancelled
            expectUnreached()
        }
        expect(2)
        // nothing is called on a disposed mono
        val sub = mono.subscribe({
            expectUnreached()
        }, {
            expectUnreached()
        })
        expect(3)
        yield() // to started coroutine
        expect(5)
        sub.dispose() // will cancel coroutine
        yield()
        finish(6)
    }

    @Test
    fun testMonoNoWait() {
        val mono = mono {
            "OK"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMonoAwait() = runBlocking {
        assertEquals("OK", Mono.just("O").awaitSingle() + "K")
    }

    @Test
    fun testMonoEmitAndAwait() {
        val mono = mono {
            Mono.just("O").awaitSingle() + "K"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMonoWithDelay() {
        val mono = mono {
            Flux.just("O").delayElements(ofMillis(50)).awaitSingle() + "K"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMonoException() {
        val mono = mono {
            Flux.just("O", "K").awaitSingle() + "K"
        }

        checkErroneous(mono) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val mono = mono {
            Flux.just("O", "#").awaitFirst() + "K"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val mono = mono {
            Flux.just("#", "O").awaitLast() + "K"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromFlux() {
        val mono = mono {
            try {
                Flux.error<String>(RuntimeException("O")).awaitFirst()
            } catch (e: RuntimeException) {
                Flux.just(e.message!!).awaitLast() + "K"
            }
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromCoroutine() {
        val mono = mono<String> {
            throw IllegalStateException(Flux.just("O").awaitSingle() + "K")
        }

        checkErroneous(mono) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }

    @Test
    fun testSuppressedException() = runTest {
        val mono = mono(currentDispatcher()) {
            launch(start = CoroutineStart.ATOMIC) {
                throw TestException() // child coroutine fails
            }
            try {
                delay(Long.MAX_VALUE)
            } finally {
                throw TestException2() // but parent throws another exception while cleaning up
            }
        }
        try {
            mono.awaitSingle()
            expectUnreached()
        } catch (e: TestException) {
            assertTrue(e.suppressed[0] is TestException2)
        }
    }

    @Test
    fun testUnhandledException() = runTest {
        expect(1)
        var subscription: Subscription? = null
        val handler = BiFunction<Throwable, Any?, Throwable> { t, _ ->
            assertTrue(t is TestException)
            expect(5)
            t
        }

        val mono = mono(currentDispatcher()) {
            expect(4)
            subscription!!.cancel() // cancel our own subscription, so that delay will get cancelled
            try {
                delay(Long.MAX_VALUE)
            } finally {
                throw TestException() // would not be able to handle it since mono is disposed
            }
        }.contextWrite { Context.of("reactor.onOperatorError.local", handler) }
        mono.subscribe(object : Subscriber<Unit> {
            override fun onSubscribe(s: Subscription) {
                expect(2)
                subscription = s
            }
            override fun onNext(t: Unit?) { expectUnreached() }
            override fun onComplete() { expectUnreached() }
            override fun onError(t: Throwable) { expectUnreached() }
        })
        expect(3)
        yield() // run coroutine
        finish(6)
    }

    @Test
    fun testIllegalArgumentException() {
        assertFailsWith<IllegalArgumentException> { mono(Job()) { } }
    }

    @Test
    fun testExceptionAfterCancellation() = runTest {
        // Test exception is not reported to global handler
        Flux
            .interval(ofMillis(1))
            .switchMap {
                mono(coroutineContext) {
                    timeBomb().awaitFirst()
                }
            }
            .onErrorReturn({
                expect(1)
                true
            }, 42)
            .blockLast()
        finish(2)
    }

    private fun timeBomb() = Mono.delay(Duration.ofMillis(1)).doOnSuccess { throw Exception("something went wrong") }

    @Test
    fun testLeakedException() = runBlocking {
        // Test exception is not reported to global handler
        val flow = mono<Unit> { throw TestException() }.toFlux().asFlow()
        repeat(10000) {
            combine(flow, flow) { _, _ -> Unit }
                .catch {}
                .collect { }
        }
    }
}
