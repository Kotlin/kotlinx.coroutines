/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.*
import kotlinx.coroutines.experimental.*
import org.junit.*
import org.junit.Assert.*
import java.io.*

/**
 * Test emitting multiple values with [rxObservable].
 */
class ObservableMultiTest : TestBase() {
    @Test
    fun testNumbers() {
        val n = 100 * stressTestMultiplier
        val observable = GlobalScope.rxObservable {
            repeat(n) { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0 until n).toList(), list)
        }
    }

    @Test
    fun testConcurrentStress() {
        val n = 10_000 * stressTestMultiplier
        val observable = GlobalScope.rxObservable {
            // concurrent emitters (many coroutines)
            val jobs = List(n) {
                // launch
                launch {
                    send(it)
                }
            }
            jobs.forEach { it.join() }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals(n, list.size)
            assertEquals((0 until n).toList(), list.sorted())
        }
    }

    @Test
    fun testIteratorResendUnconfined() {
        val n = 10_000 * stressTestMultiplier
        val observable = GlobalScope.rxObservable(Unconfined) {
            Observable.range(0, n).consumeEach { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0 until n).toList(), list)
        }
    }

    @Test
    fun testIteratorResendPool() {
        val n = 10_000 * stressTestMultiplier
        val observable = GlobalScope.rxObservable {
            Observable.range(0, n).consumeEach { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0 until n).toList(), list)
        }
    }

    @Test
    fun testSendAndCrash() {
        val observable = GlobalScope.rxObservable {
            send("O")
            throw IOException("K")
        }
        val single = GlobalScope.rxSingle {
            var result = ""
            try {
                observable.consumeEach { result += it }
            } catch(e: IOException) {
                result += e.message
            }
            result
        }
        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }
}