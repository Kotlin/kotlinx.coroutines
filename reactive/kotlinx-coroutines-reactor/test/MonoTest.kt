/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.reactive.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import reactor.core.publisher.*
import java.time.Duration.*

class MonoTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("timer-", "parallel-")
    }

    @Test
    fun testBasicSuccess() = runBlocking {
        expect(1)
        val mono = mono {
            expect(4)
            "OK"
        }
        expect(2)
        mono.subscribe { value ->
            expect(5)
            Assert.assertThat(value, IsEqual("OK"))
        }
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicFailure() = runBlocking {
        expect(1)
        val mono = mono(NonCancellable) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        mono.subscribe({
            expectUnreached()
        }, { error ->
            expect(5)
            Assert.assertThat(error, IsInstanceOf(RuntimeException::class.java))
            Assert.assertThat(error.message, IsEqual("OK"))
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicEmpty() = runBlocking {
        expect(1)
        val mono = mono {
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
        val mono = mono {
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
        val mono = GlobalScope.mono {
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
        val mono = GlobalScope.mono {
            Mono.just("O").awaitSingle() + "K"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMonoWithDelay() {
        val mono = GlobalScope.mono {
            Flux.just("O").delayElements(ofMillis(50)).awaitSingle() + "K"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMonoException() {
        val mono = GlobalScope.mono {
            Flux.just("O", "K").awaitSingle() + "K"
        }

        checkErroneous(mono) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val mono = GlobalScope.mono {
            Flux.just("O", "#").awaitFirst() + "K"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val mono = GlobalScope.mono {
            Flux.just("#", "O").awaitLast() + "K"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromFlux() {
        val mono = GlobalScope.mono {
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
        val mono = GlobalScope.mono<String> {
            throw IllegalStateException(Flux.just("O").awaitSingle() + "K")
        }

        checkErroneous(mono) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }

    @Test
    fun testCancelsParentOnFailure() = runTest(
        expected = { it is RuntimeException && it.message == "OK" }
    ) {
        // has parent, so should cancel it on failure
        mono<Unit> {
            throw RuntimeException("OK")
        }.subscribe(
            { expectUnreached() },
            { assert(it is RuntimeException) }
        )
    }
}
