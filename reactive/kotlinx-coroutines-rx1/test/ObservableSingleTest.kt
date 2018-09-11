/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx1

import kotlinx.coroutines.experimental.*
import org.junit.*
import org.junit.Assert.*
import rx.*
import java.util.concurrent.*

class ObservableSingleTest {
    @Test
    fun testSingleNoWait() {
        val observable = GlobalScope.rxObservable {
            send("OK")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleNullNoWait() {
        val observable = GlobalScope.rxObservable<String?> {
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
        val observable = GlobalScope.rxObservable {
            send(Observable.just("O").awaitSingle() + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleWithDelay() {
        val observable = GlobalScope.rxObservable {
            send(Observable.timer(50, TimeUnit.MILLISECONDS).map { "O" }.awaitSingle() + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleException() {
        val observable = GlobalScope.rxObservable {
            send(Observable.just("O", "K").awaitSingle() + "K")
        }

        checkErroneous(observable) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val observable = GlobalScope.rxObservable {
            send(Observable.just("O", "#").awaitFirst() + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrDefault() {
        val observable = GlobalScope.rxObservable {
            send(Observable.empty<String>().awaitFirstOrDefault("O") + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrDefaultWithValues() {
        val observable = GlobalScope.rxObservable {
            send(Observable.just("O", "#").awaitFirstOrDefault("!") + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrNull() {
        val observable = GlobalScope.rxObservable<String> {
            send(Observable.empty<String>().awaitFirstOrNull() ?: "OK")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrNullWithValues() {
        val observable = GlobalScope.rxObservable {
            send((Observable.just("O", "#").awaitFirstOrNull() ?: "!") + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrElse() {
        val observable = GlobalScope.rxObservable {
            send(Observable.empty<String>().awaitFirstOrElse { "O" } + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrElseWithValues() {
        val observable = GlobalScope.rxObservable {
            send(Observable.just("O", "#").awaitFirstOrElse { "!" } + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val observable = GlobalScope.rxObservable {
            send(Observable.just("#", "O").awaitLast() + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val observable = GlobalScope.rxObservable {
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
        val observable = GlobalScope.rxObservable<String> {
            error(Observable.just("O").awaitSingle() + "K")
        }

        checkErroneous(observable) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }

    @Test
    fun testObservableIteration() {
        val observable = GlobalScope.rxObservable {
            var result = ""
            Observable.just("O", "K").consumeEach {result += it }
            send(result)
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testObservableIterationFailure() {
        val observable = GlobalScope.rxObservable {
            try {
                Observable.error<String>(RuntimeException("OK")).consumeEach { fail("Should not be here") }
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
