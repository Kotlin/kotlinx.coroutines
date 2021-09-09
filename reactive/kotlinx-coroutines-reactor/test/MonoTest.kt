/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.CancellationException
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.*
import org.junit.Test
import org.reactivestreams.*
import reactor.core.publisher.*
import reactor.util.context.*
import java.time.Duration.*
import java.util.function.*
import kotlin.test.*

class MonoTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("timer-", "parallel-")
        Hooks.onErrorDropped { expectUnreached() }
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
        assertEquals("OK", Mono.just("O").awaitSingleOrNull() + "K")
        assertFailsWith<NoSuchElementException>{ Mono.empty<String>().awaitSingle() }
        assertNull(Mono.empty<Int>().awaitSingleOrNull())
    }

    /** Tests that the versions of the await methods specialized for Mono for deprecation behave correctly and we don't
     * break any code by introducing them. */
    @Test
    @Suppress("DEPRECATION")
    fun testDeprecatedAwaitMethods() = runBlocking {
        val filledMono = mono<String> { "OK" }
        assertEquals("OK", filledMono.awaitFirst())
        assertEquals("OK", filledMono.awaitFirstOrDefault("!"))
        assertEquals("OK", filledMono.awaitFirstOrNull())
        assertEquals("OK", filledMono.awaitFirstOrElse { "ELSE" })
        assertEquals("OK", filledMono.awaitLast())
        assertEquals("OK", filledMono.awaitSingleOrDefault("!"))
        assertEquals("OK", filledMono.awaitSingleOrElse { "ELSE" })
        val emptyMono = mono<String> { null }
        assertFailsWith<NoSuchElementException> { emptyMono.awaitFirst() }
        assertEquals("OK", emptyMono.awaitFirstOrDefault("OK"))
        assertNull(emptyMono.awaitFirstOrNull())
        assertEquals("ELSE", emptyMono.awaitFirstOrElse { "ELSE" })
        assertFailsWith<NoSuchElementException> { emptyMono.awaitLast() }
        assertEquals("OK", emptyMono.awaitSingleOrDefault("OK"))
        assertEquals("ELSE", emptyMono.awaitSingleOrElse { "ELSE" })
    }

    /** Tests that calls to [awaitSingleOrNull] (and, thus, to the rest of such functions) throw [CancellationException]
     * and unsubscribe from the publisher when their [Job] is cancelled. */
    @Test
    fun testAwaitCancellation() = runTest {
        expect(1)
        val mono = mono { delay(Long.MAX_VALUE) }.doOnSubscribe { expect(3) }.doOnCancel { expect(5) }
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            try {
                expect(2)
                mono.awaitSingleOrNull()
            } catch (e: CancellationException) {
                expect(6)
                throw e
            }
        }
        expect(4)
        job.cancelAndJoin()
        finish(7)
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
                    timeBomb().awaitSingle()
                }
            }
            .onErrorReturn({
                expect(1)
                true
            }, 42)
            .blockLast()
        finish(2)
    }

    private fun timeBomb() = Mono.delay(ofMillis(1)).doOnSuccess { throw Exception("something went wrong") }

    @Test
    fun testLeakedException() = runBlocking {
        // Test exception is not reported to global handler
        val flow = mono<Unit> { throw TestException() }.toFlux().asFlow()
        repeat(10000) {
            combine(flow, flow) { _, _ -> }
                .catch {}
                .collect { }
        }
    }

    /** Test that cancelling a [mono] due to a timeout does throw an exception. */
    @Test
    fun testTimeout() {
        val mono = mono {
            withTimeout(1) { delay(100) }
        }
        try {
            mono.doOnSubscribe { expect(1) }
                .doOnNext { expectUnreached() }
                .doOnSuccess { expectUnreached() }
                .doOnError { expect(2) }
                .doOnCancel { expectUnreached() }
                .block()
        } catch (e: CancellationException) {
            expect(3)
        }
        finish(4)
    }

    /** Test that when the reason for cancellation of a [mono] is that the downstream doesn't want its results anymore,
     * this is considered normal behavior and exceptions are not propagated. */
    @Test
    fun testDownstreamCancellationDoesNotThrow() = runTest {
        var i = 0
        /** Attach a hook that handles exceptions from publishers that are known to be disposed of. We don't expect it
         * to be fired in this case, as the reason for the publisher in this test to accept an exception is simply
         * cancellation from the downstream. */
        Hooks.onOperatorError("testDownstreamCancellationDoesNotThrow") { t, a ->
            expectUnreached()
            t
        }
        /** A Mono that doesn't emit a value and instead waits indefinitely. */
        val mono = mono(Dispatchers.Unconfined) { expect(5 * i + 3); delay(Long.MAX_VALUE) }
            .doOnSubscribe { expect(5 * i + 2) }
            .doOnNext { expectUnreached() }
            .doOnSuccess { expectUnreached() }
            .doOnError { expectUnreached() }
            .doOnCancel { expect(5 * i + 4) }
        val n = 1000
        repeat(n) {
            i = it
            expect(5 * i + 1)
            mono.awaitCancelAndJoin()
            expect(5 * i + 5)
        }
        finish(5 * n + 1)
        Hooks.resetOnOperatorError("testDownstreamCancellationDoesNotThrow")
    }

    /** Test that, when [Mono] is cancelled by the downstream and throws during handling the cancellation, the resulting
     * error is propagated to [Hooks.onOperatorError]. */
    @Test
    fun testRethrowingDownstreamCancellation() = runTest {
        var i = 0
        /** Attach a hook that handles exceptions from publishers that are known to be disposed of. We expect it
         * to be fired in this case. */
        Hooks.onOperatorError("testDownstreamCancellationDoesNotThrow") { t, a ->
            expect(i * 6 + 5)
            t
        }
        /** A Mono that doesn't emit a value and instead waits indefinitely, and, when cancelled, throws. */
        val mono = mono(Dispatchers.Unconfined) {
            expect(i * 6 + 3)
            try {
                delay(Long.MAX_VALUE)
            } catch (e: CancellationException) {
                throw TestException()
            }
        }
            .doOnSubscribe { expect(i * 6 + 2) }
            .doOnNext { expectUnreached() }
            .doOnSuccess { expectUnreached() }
            .doOnError { expectUnreached() }
            .doOnCancel { expect(i * 6 + 4) }
        val n = 1000
        repeat(n) {
            i = it
            expect(i * 6 + 1)
            mono.awaitCancelAndJoin()
            expect(i * 6 + 6)
        }
        finish(n * 6 + 1)
        Hooks.resetOnOperatorError("testDownstreamCancellationDoesNotThrow")
    }

    /** Run the given [Mono], cancel it, wait for the cancellation handler to finish, and return only then.
     *
     * Will not work in the general case, but here, when the publisher uses [Dispatchers.Unconfined], this seems to
     * ensure that the cancellation handler will have nowhere to execute but serially with the cancellation. */
    private suspend fun <T> Mono<T>.awaitCancelAndJoin() = coroutineScope {
        async(start = CoroutineStart.UNDISPATCHED) {
            awaitSingleOrNull()
        }.cancelAndJoin()
    }
}
