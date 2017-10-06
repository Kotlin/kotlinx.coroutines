/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.CommonPool
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
        val flux = flux(CommonPool) {
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
        val flux = flux(CommonPool) {
            send(Flux.just("O").awaitSingle() + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleWithDelay() {
        val flux = flux(CommonPool) {
            send(Flux.just("O").delayElements(ofMillis(50)).awaitSingle() + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleException() {
        val flux = flux(CommonPool) {
            send(Flux.just("O", "K").awaitSingle() + "K")
        }

        checkErroneous(flux) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val flux = flux(CommonPool) {
            send(Flux.just("O", "#").awaitFirst() + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrDefault() {
        val flux = flux(CommonPool) {
            send(Flux.empty<String>().awaitFirstOrDefault("O") + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrDefaultWithValues() {
        val flux = flux(CommonPool) {
            send(Flux.just("O", "#").awaitFirstOrDefault("!") + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val flux = flux(CommonPool) {
            send(Flux.just("#", "O").awaitLast() + "K")
        }

        checkSingleValue(flux) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val flux = flux(CommonPool) {
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
        val flux = flux<String>(CommonPool) {
            error(Flux.just("O").awaitSingle() + "K")
        }

        checkErroneous(flux) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }

    @Test
    fun testFluxIteration() {
        val flux = flux(CommonPool) {
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
        val flux = flux(CommonPool) {
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
