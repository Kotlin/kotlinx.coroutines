/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.reactive.*
import org.junit.*
import org.junit.Assert.*
import reactor.core.publisher.*
import java.io.*

class FluxMultiTest : TestBase() {
    @Test
    fun testNumbers() {
        val n = 100 * stressTestMultiplier
        val flux = flux {
            repeat(n) { send(it) }
        }
        checkMonoValue(flux.collectList()) { list ->
            assertEquals((0 until n).toList(), list)
        }
    }

    @Test
    fun testConcurrentStress() {
        val n = 10_000 * stressTestMultiplier
        val flux = flux {
            // concurrent emitters (many coroutines)
            val jobs = List(n) {
                // launch
                launch {
                    send(it)
                }
            }
            jobs.forEach { it.join() }
        }
        checkMonoValue(flux.collectList()) { list ->
            assertEquals(n, list.size)
            assertEquals((0 until n).toList(), list.sorted())
        }
    }

    @Test
    fun testIteratorResendUnconfined() {
        val n = 10_000 * stressTestMultiplier
        val flux = flux(Dispatchers.Unconfined) {
            Flux.range(0, n).collect { send(it) }
        }
        checkMonoValue(flux.collectList()) { list ->
            assertEquals((0 until n).toList(), list)
        }
    }

    @Test
    fun testIteratorResendPool() {
        val n = 10_000 * stressTestMultiplier
        val flux = flux {
            Flux.range(0, n).collect { send(it) }
        }
        checkMonoValue(flux.collectList()) { list ->
            assertEquals((0 until n).toList(), list)
        }
    }

    @Test
    fun testSendAndCrash() {
        val flux = flux {
            send("O")
            throw IOException("K")
        }
        val mono = mono {
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