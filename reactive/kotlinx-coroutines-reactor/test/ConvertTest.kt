/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.reactive.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class ConvertTest : TestBase() {
    @Test
    fun testJobToMonoSuccess() = runBlocking {
        expect(1)
        val job = launch {
            expect(3)
        }
        val mono = job.asMono(coroutineContext.minusKey(Job))
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
        val job = async(NonCancellable) {
            expect(3)
            throw RuntimeException("OK")
        }
        val mono = job.asMono(coroutineContext.minusKey(Job))
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
        val d = GlobalScope.async {
            delay(50)
            "OK"
        }
        val mono1 = d.asMono(Dispatchers.Unconfined)
        checkMonoValue(mono1) {
            assertEquals("OK", it)
        }
        val mono2 = d.asMono(Dispatchers.Unconfined)
        checkMonoValue(mono2) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testDeferredToMonoEmpty() {
        val d = GlobalScope.async {
            delay(50)
            null
        }
        val mono1 = d.asMono(Dispatchers.Unconfined)
        checkMonoValue(mono1, Assert::assertNull)
        val mono2 = d.asMono(Dispatchers.Unconfined)
        checkMonoValue(mono2, Assert::assertNull)
    }

    @Test
    fun testDeferredToMonoFail() {
        val d = GlobalScope.async {
            delay(50)
            throw TestRuntimeException("OK")
        }
        val mono1 = d.asMono(Dispatchers.Unconfined)
        checkErroneous(mono1) {
            check(it is TestRuntimeException && it.message == "OK") { "$it" }
        }
        val mono2 = d.asMono(Dispatchers.Unconfined)
        checkErroneous(mono2) {
            check(it is TestRuntimeException && it.message == "OK") { "$it" }
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
        val flux = c.asFlux(Dispatchers.Unconfined)
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
        val flux = c.asFlux(Dispatchers.Unconfined)
        val mono = mono(Dispatchers.Unconfined) {
            var result = ""
            try {
                flux.collect { result += it }
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