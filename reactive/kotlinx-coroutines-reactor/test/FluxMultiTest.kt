/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.reactor

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.Unconfined
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.reactive.consumeEach
import org.junit.Assert.assertEquals
import org.junit.Test
import reactor.core.publisher.Flux
import java.io.IOException

/**
 * Test emitting multiple values with [flux].
 */
class FluxMultiTest : TestBase() {
    @Test
    fun testNumbers() {
        val n = 100 * stressTestMultiplier
        val flux = flux(CommonPool) {
            repeat(n) { send(it) }
        }
        checkMonoValue(flux.collectList()) { list ->
            assertEquals((0..n - 1).toList(), list)
        }
    }

    @Test
    fun testConcurrentStress() {
        val n = 10_000 * stressTestMultiplier
        val flux = flux<Int>(CommonPool) {
            // concurrent emitters (many coroutines)
            val jobs = List(n) {
                // launch
                launch(CommonPool) {
                    send(it)
                }
            }
            jobs.forEach { it.join() }
        }
        checkMonoValue(flux.collectList()) { list ->
            assertEquals(n, list.size)
            assertEquals((0..n - 1).toList(), list.sorted())
        }
    }

    @Test
    fun testIteratorResendUnconfined() {
        val n = 10_000 * stressTestMultiplier
        val flux = flux(Unconfined) {
            Flux.range(0, n).consumeEach { send(it) }
        }
        checkMonoValue(flux.collectList()) { list ->
            assertEquals((0..n - 1).toList(), list)
        }
    }

    @Test
    fun testIteratorResendPool() {
        val n = 10_000 * stressTestMultiplier
        val flux = flux(CommonPool) {
            Flux.range(0, n).consumeEach { send(it) }
        }
        checkMonoValue(flux.collectList()) { list ->
            assertEquals((0..n - 1).toList(), list)
        }
    }

    @Test
    fun testSendAndCrash() {
        val flux = flux(CommonPool) {
            send("O")
            throw IOException("K")
        }
        val mono = mono(CommonPool) {
            var result = ""
            try {
                flux.consumeEach { result += it }
            } catch(e: IOException) {
                result += e.message
            }
            result
        }
        checkMonoValue(mono) {
            assertEquals("OK", it)
        }
    }
}