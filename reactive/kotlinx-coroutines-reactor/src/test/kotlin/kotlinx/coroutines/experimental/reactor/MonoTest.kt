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

import guide.test.ignoreLostThreads
import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.reactive.awaitFirst
import kotlinx.coroutines.experimental.reactive.awaitLast
import kotlinx.coroutines.experimental.reactive.awaitSingle
import kotlinx.coroutines.experimental.runBlocking
import kotlinx.coroutines.experimental.yield
import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsInstanceOf
import org.junit.Assert
import org.junit.Assert.assertEquals
import org.junit.Before
import org.junit.Test
import reactor.core.publisher.Flux
import reactor.core.publisher.Mono

/**
 * Tests emitting single item with [mono].
 */
class MonoTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("timer-", "parallel-")
    }

    @Test
    fun testBasicSuccess() = runBlocking {
        expect(1)
        val mono = mono(coroutineContext) {
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
        val mono = mono(coroutineContext) {
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
        val mono = mono(coroutineContext) {
            expect(4)
            null
        }
        expect(2)
        mono.subscribe ({}, { throw it }, {
            expect(5)
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicUnsubscribe() = runBlocking {
        expect(1)
        val mono = mono(coroutineContext) {
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
        val mono = mono(CommonPool) {
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
        val mono = mono(CommonPool) {
            Mono.just("O").awaitSingle() + "K"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMonoWithDelay() {
        val mono = mono(CommonPool) {
            Flux.just("O").delayMillis(50).awaitSingle() + "K"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMonoException() {
        val mono = mono(CommonPool) {
            Flux.just("O", "K").awaitSingle() + "K"
        }

        checkErroneous(mono) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val mono = mono(CommonPool) {
            Flux.just("O", "#").awaitFirst() + "K"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val mono = mono(CommonPool) {
            Flux.just("#", "O").awaitLast() + "K"
        }

        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromFlux() {
        val mono = mono(CommonPool) {
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
        val mono = mono<String>(CommonPool) {
            throw IllegalStateException(Flux.just("O").awaitSingle() + "K")
        }

        checkErroneous(mono) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }
}
