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
import kotlinx.coroutines.experimental.NonCancellable
import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.Unconfined
import kotlinx.coroutines.experimental.async
import kotlinx.coroutines.experimental.channels.produce
import kotlinx.coroutines.experimental.delay
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.reactive.consumeEach
import kotlinx.coroutines.experimental.runBlocking
import kotlinx.coroutines.experimental.yield
import org.junit.Assert.assertEquals
import org.junit.Assert.assertNull
import org.junit.Assert.fail
import org.junit.Test

class ConvertTest : TestBase() {
    class TestException(s: String): RuntimeException(s)

    @Test
    fun testJobToMonoSuccess() = runBlocking<Unit> {
        expect(1)
        val job = launch(coroutineContext) {
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
    fun testJobToMonoFail() = runBlocking<Unit> {
        expect(1)
        val job = async(coroutineContext + NonCancellable) { // don't kill parent on exception
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
        val d = async(CommonPool) {
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
        val d = async(CommonPool) {
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
        val d = async(CommonPool) {
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
        val c = produce(CommonPool) {
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
        val c = produce(CommonPool) {
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