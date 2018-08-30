/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.channels.*
import kotlinx.coroutines.experimental.reactive.*
import org.junit.*
import org.junit.Assert.*

class ConvertTest : TestBase() {
    class TestException(s: String): RuntimeException(s)

    @Test
    fun testJobToMonoSuccess() = runBlocking {
        expect(1)
        val job = launch {
            expect(3)
        }
        val mono = job.asMono(coroutineContext)
        mono.subscribe {
            expect(4)
        }
        expect(2)
        yield()
        finish(5)
    }

    @Test
    fun testJobToMonoFail() = runBlocking {
        expect(1)
        val job = async(NonCancellable) { // don't kill parent on exception
            expect(3)
            throw RuntimeException("OK")
        }
        val mono = job.asMono(coroutineContext)
        mono.subscribe(
                { fail("no item should be emitted") },
                { expect(4) }
        )
        expect(2)
        yield()
        finish(5)
    }

    @Test
    fun testDeferredToMono() {
        val d = async {
            delay(50)
            "OK"
        }
        val mono1 = d.asMono(Unconfined)
        checkMonoValue(mono1) {
            assertEquals("OK", it)
        }
        val mono2 = d.asMono(Unconfined)
        checkMonoValue(mono2) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testDeferredToMonoEmpty() {
        val d = async {
            delay(50)
            null
        }
        val mono1 = d.asMono(Unconfined)
        checkMonoValue(mono1, ::assertNull)
        val mono2 = d.asMono(Unconfined)
        checkMonoValue(mono2, ::assertNull)
    }

    @Test
    fun testDeferredToMonoFail() {
        val d = GlobalScope.async {
            delay(50)
            throw TestException("OK")
        }
        val mono1 = d.asMono(Unconfined)
        checkErroneous(mono1) {
            check(it is TestException && it.message == "OK") { "$it" }
        }
        val mono2 = d.asMono(Unconfined)
        checkErroneous(mono2) {
            check(it is TestException && it.message == "OK") { "$it" }
        }
    }

    @Test
    fun testToFlux() {
        val c = GlobalScope.produce {
            delay(50)
            send("O")
            delay(50)
            send("K")
        }
        val flux = c.asFlux(Unconfined)
        checkMonoValue(flux.reduce { t1, t2 -> t1 + t2 }) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testToFluxFail() {
        val c = GlobalScope.produce {
            delay(50)
            send("O")
            delay(50)
            throw TestException("K")
        }
        val flux = c.asFlux(Unconfined)
        val mono = mono(Unconfined) {
            var result = ""
            try {
                flux.consumeEach { result += it }
            } catch(e: Throwable) {
                check(e is TestException)
                result += e.message
            }
            result
        }
        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }
}