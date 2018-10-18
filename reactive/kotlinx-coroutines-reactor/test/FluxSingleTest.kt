/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.reactive.*
import org.junit.*
import org.junit.Assert.*
import reactor.core.publisher.*
import java.time.Duration.*

class FluxSingleTest {
    @Test
    fun testSingleNoWait() {
        val flux = GlobalScope.flux {
            send("OK")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleAwait() = runBlocking {
        assertEquals("OK", Flux.just("O").awaitSingle() + "K")
    }

    @Test
    fun testSingleEmitAndAwait() {
        val flux = GlobalScope.flux {
            send(Flux.just("O").awaitSingle() + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleWithDelay() {
        val flux = GlobalScope.flux {
            send(Flux.just("O").delayElements(ofMillis(50)).awaitSingle() + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleException() {
        val flux = GlobalScope.flux {
            send(Flux.just("O", "K").awaitSingle() + "K")
        }

        checkErroneous(flux) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val flux = GlobalScope.flux {
            send(Flux.just("O", "#").awaitFirst() + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrDefault() {
        val flux = GlobalScope.flux {
            send(Flux.empty<String>().awaitFirstOrDefault("O") + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrDefaultWithValues() {
        val flux = GlobalScope.flux {
            send(Flux.just("O", "#").awaitFirstOrDefault("!") + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrNull() {
        val flux = GlobalScope.flux<String> {
            send(Flux.empty<String>().awaitFirstOrNull() ?: "OK")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrNullWithValues() {
        val flux = GlobalScope.flux {
            send((Flux.just("O", "#").awaitFirstOrNull() ?: "!") + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrElse() {
        val flux = GlobalScope.flux {
            send(Flux.empty<String>().awaitFirstOrElse { "O" } + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrElseWithValues() {
        val flux = GlobalScope.flux {
            send(Flux.just("O", "#").awaitFirstOrElse { "!" } + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val flux = GlobalScope.flux {
            send(Flux.just("#", "O").awaitLast() + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val flux = GlobalScope.flux {
            try {
                send(Flux.error<String>(RuntimeException("O")).awaitFirst())
            } catch (e: RuntimeException) {
                send(Flux.just(e.message!!).awaitLast() + "K")
            }
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromCoroutine() {
        val flux = GlobalScope.flux<String> {
            error(Flux.just("O").awaitSingle() + "K")
        }

        checkErroneous(flux) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }

    @Test
    fun testFluxIteration() {
        val flux = GlobalScope.flux {
            var result = ""
            Flux.just("O", "K").consumeEach { result += it }
            send(result)
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testFluxIterationFailure() {
        val flux = GlobalScope.flux {
            try {
                Flux.error<String>(RuntimeException("OK")).consumeEach { fail("Should not be here") }
                send("Fail")
            } catch (e: RuntimeException) {
                send(e.message!!)
            }
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }
}
