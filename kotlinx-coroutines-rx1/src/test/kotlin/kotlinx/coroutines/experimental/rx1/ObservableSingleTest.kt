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

package kotlinx.coroutines.experimental.rx1

import kotlinx.coroutines.experimental.CommonPool
import kotlinx.coroutines.experimental.runBlocking
import org.junit.Assert.assertEquals
import org.junit.Assert.fail
import org.junit.Test
import rx.Observable
import java.util.concurrent.TimeUnit

/**
 * Tests emitting single item with [rxObservable].
 */
class ObservableSingleTest {
    @Test
    fun testSingleNoWait() {
        val observable = rxObservable(CommonPool) {
            send("OK")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleNullNoWait() {
        val observable = rxObservable<String?>(CommonPool) {
            send(null)
        }

        checkSingleValue(observable) {
            assertEquals(null, it)
        }
    }

    @Test
    fun testSingleAwait() = runBlocking {
        assertEquals("OK", Observable.just("O").awaitSingle() + "K")
    }

    @Test
    fun testSingleEmitAndAwait() {
        val observable = rxObservable(CommonPool) {
            send(Observable.just("O").awaitSingle() + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleWithDelay() {
        val observable = rxObservable(CommonPool) {
            send(Observable.timer(50, TimeUnit.MILLISECONDS).map { "O" }.awaitSingle() + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleException() {
        val observable = rxObservable(CommonPool) {
            send(Observable.just("O", "K").awaitSingle() + "K")
        }

        checkErroneous(observable) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val observable = rxObservable(CommonPool) {
            send(Observable.just("O", "#").awaitFirst() + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val observable = rxObservable(CommonPool) {
            send(Observable.just("#", "O").awaitLast() + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val observable = rxObservable(CommonPool) {
            try {
                send(Observable.error<String>(RuntimeException("O")).awaitFirst())
            } catch (e: RuntimeException) {
                send(Observable.just(e.message!!).awaitLast() + "K")
            }
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromCoroutine() {
        val observable = rxObservable<String>(CommonPool) {
            error(Observable.just("O").awaitSingle() + "K")
        }

        checkErroneous(observable) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }

    @Test
    fun testObservableIteration() {
        val observable = rxObservable(CommonPool) {
            var result = ""
            for (x in Observable.just("O", "K"))
                result += x
            send(result)
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testObservableIterationFailure() {
        val observable = rxObservable(CommonPool) {
            try {
                for (x in Observable.error<String>(RuntimeException("OK")))
                    fail("Should not be here")
                send("Fail")
            } catch (e: RuntimeException) {
                send(e.message!!)
            }
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }
}
