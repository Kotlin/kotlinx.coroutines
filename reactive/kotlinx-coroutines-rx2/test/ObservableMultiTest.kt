/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.Observable
import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.Unconfined
import kotlinx.coroutines.experimental.launch
import org.junit.Assert.assertEquals
import org.junit.Test
import java.io.IOException

/**
 * Test emitting multiple values with [rxObservable].
 */
class ObservableMultiTest : TestBase() {
    @Test
    fun testNumbers() {
        val n = 100 * stressTestMultiplier
        val observable = rxObservable(CommonPool) {
            repeat(n) { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0..n - 1).toList(), list)
        }
    }

    @Test
    fun testConcurrentStress() {
        val n = 10_000 * stressTestMultiplier
        val observable = rxObservable<Int>(CommonPool) {
            // concurrent emitters (many coroutines)
            val jobs = List(n) {
                // launch
                launch(CommonPool) {
                    send(it)
                }
            }
            jobs.forEach { it.join() }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals(n, list.size)
            assertEquals((0..n - 1).toList(), list.sorted())
        }
    }

    @Test
    fun testIteratorResendUnconfined() {
        val n = 10_000 * stressTestMultiplier
        val observable = rxObservable(Unconfined) {
            Observable.range(0, n).consumeEach { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0..n - 1).toList(), list)
        }
    }

    @Test
    fun testIteratorResendPool() {
        val n = 10_000 * stressTestMultiplier
        val observable = rxObservable(CommonPool) {
            Observable.range(0, n).consumeEach { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0..n - 1).toList(), list)
        }
    }

    @Test
    fun testSendAndCrash() {
        val observable = rxObservable(CommonPool) {
            send("O")
            throw IOException("K")
        }
        val single = rxSingle(CommonPool) {
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