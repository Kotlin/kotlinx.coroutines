/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.DefaultDispatcher
import kotlinx.coroutines.experimental.reactive.*
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Assert.assertEquals
import org.junit.Assert.fail
import org.junit.Test
import reactor.core.publisher.Flux
import java.time.Duration.ofMillis

/**
 * Tests emitting single item with [flux].
 */
class FluxSingleTest {
    @Test
    fun testSingleNoWait() {
        val flux = flux(DefaultDispatcher) {
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
        val flux = flux(DefaultDispatcher) {
            send(Flux.just("O").awaitSingle() + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleWithDelay() {
        val flux = flux(DefaultDispatcher) {
            send(Flux.just("O").delayElements(ofMillis(50)).awaitSingle() + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleException() {
        val flux = flux(DefaultDispatcher) {
            send(Flux.just("O", "K").awaitSingle() + "K")
        }

        checkErroneous(flux) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val flux = flux(DefaultDispatcher) {
            send(Flux.just("O", "#").awaitFirst() + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrDefault() {
        val flux = flux(DefaultDispatcher) {
            send(Flux.empty<String>().awaitFirstOrDefault("O") + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrDefaultWithValues() {
        val flux = flux(DefaultDispatcher) {
            send(Flux.just("O", "#").awaitFirstOrDefault("!") + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrNull() {
        val flux = flux<String>(DefaultDispatcher) {
            send(Flux.empty<String>().awaitFirstOrNull() ?: "OK")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrNullWithValues() {
        val flux = flux(DefaultDispatcher) {
            send((Flux.just("O", "#").awaitFirstOrNull() ?: "!") + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrElse() {
        val flux = flux(DefaultDispatcher) {
            send(Flux.empty<String>().awaitFirstOrElse { "O" } + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrElseWithValues() {
        val flux = flux(DefaultDispatcher) {
            send(Flux.just("O", "#").awaitFirstOrElse { "!" } + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val flux = flux(DefaultDispatcher) {
            send(Flux.just("#", "O").awaitLast() + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val flux = flux(DefaultDispatcher) {
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
        val flux = flux<String>(DefaultDispatcher) {
            error(Flux.just("O").awaitSingle() + "K")
        }

        checkErroneous(flux) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }

    @Test
    fun testFluxIteration() {
        val flux = flux(DefaultDispatcher) {
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
        val flux = flux(DefaultDispatcher) {
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
