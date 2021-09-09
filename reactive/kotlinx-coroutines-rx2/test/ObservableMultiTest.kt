/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import kotlinx.coroutines.*
import org.junit.Test
import java.io.*
import kotlin.test.*

/**
 * Test emitting multiple values with [rxObservable].
 */
class ObservableMultiTest : TestBase() {
    @Test
    fun testNumbers() {
        val n = 100 * stressTestMultiplier
        val observable = rxObservable {
            repeat(n) { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0 until n).toList(), list)
        }
    }


    @Test
    fun testConcurrentStress() {
        val n = 10_000 * stressTestMultiplier
        val observable = rxObservable {
            newCoroutineContext(coroutineContext)
            // concurrent emitters (many coroutines)
            val jobs = List(n) {
                // launch
                launch {
                    val i = it
                    send(i)
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
        val observable = rxObservable(Dispatchers.Unconfined) {
            Observable.range(0, n).collect { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0 until n).toList(), list)
        }
    }

    @Test
    fun testIteratorResendPool() {
        val n = 10_000 * stressTestMultiplier
        val observable = rxObservable {
            Observable.range(0, n).collect { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0 until n).toList(), list)
        }
    }

    @Test
    fun testSendAndCrash() {
        val observable = rxObservable {
            send("O")
            throw IOException("K")
        }
        val single = rxSingle {
            var result = ""
            try {
                observable.collect { result += it }
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