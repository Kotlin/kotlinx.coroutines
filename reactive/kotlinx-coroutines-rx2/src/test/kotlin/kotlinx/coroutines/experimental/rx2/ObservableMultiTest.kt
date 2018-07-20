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

package kotlinx.coroutines.experimental.rx2

import io.reactivex.Observable
import kotlinx.coroutines.experimental.DefaultDispatcher
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
        val observable = rxObservable(DefaultDispatcher) {
            repeat(n) { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0..n - 1).toList(), list)
        }
    }

    @Test
    fun testConcurrentStress() {
        val n = 10_000 * stressTestMultiplier
        val observable = rxObservable<Int>(DefaultDispatcher) {
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
        val observable = rxObservable(DefaultDispatcher) {
            Observable.range(0, n).consumeEach { send(it) }
        }
        checkSingleValue(observable.toList()) { list ->
            assertEquals((0..n - 1).toList(), list)
        }
    }

    @Test
    fun testSendAndCrash() {
        val observable = rxObservable(DefaultDispatcher) {
            send("O")
            throw IOException("K")
        }
        val single = rxSingle(DefaultDispatcher) {
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