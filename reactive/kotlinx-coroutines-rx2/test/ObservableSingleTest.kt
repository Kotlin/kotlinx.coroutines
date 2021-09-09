/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class ObservableSingleTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    @Test
    fun testSingleNoWait() {
        val observable = rxObservable {
            send("OK")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleAwait() = runBlocking {
        assertEquals("OK", Observable.just("O").awaitSingle() + "K")
    }

    @Test
    fun testSingleEmitAndAwait() {
        val observable = rxObservable {
            send(Observable.just("O").awaitSingle() + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleWithDelay() {
        val observable = rxObservable {
            send(Observable.timer(50, TimeUnit.MILLISECONDS).map { "O" }.awaitSingle() + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleException() {
        val observable = rxObservable {
            send(Observable.just("O", "K").awaitSingle() + "K")
        }

        checkErroneous(observable) {
            assertTrue(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val observable = rxObservable {
            send(Observable.just("O", "#").awaitFirst() + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrDefault() {
        val observable = rxObservable {
            send(Observable.empty<String>().awaitFirstOrDefault("O") + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrDefaultWithValues() {
        val observable = rxObservable {
            send(Observable.just("O", "#").awaitFirstOrDefault("!") + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrNull() {
        val observable = rxObservable<String> {
            send(Observable.empty<String>().awaitFirstOrNull() ?: "OK")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrNullWithValues() {
        val observable = rxObservable {
            send((Observable.just("O", "#").awaitFirstOrNull() ?: "!") + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrElse() {
        val observable = rxObservable {
            send(Observable.empty<String>().awaitFirstOrElse { "O" } + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitFirstOrElseWithValues() {
        val observable = rxObservable {
            send(Observable.just("O", "#").awaitFirstOrElse { "!" } + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val observable = rxObservable {
            send(Observable.just("#", "O").awaitLast() + "K")
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val observable = rxObservable {
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
        val observable = rxObservable<String> {
            throw IllegalStateException(Observable.just("O").awaitSingle() + "K")
        }

        checkErroneous(observable) {
            assertTrue(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }

    @Test
    fun testObservableIteration() {
        val observable = rxObservable {
            var result = ""
            Observable.just("O", "K").collect { result += it }
            send(result)
        }

        checkSingleValue(observable) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testObservableIterationFailure() {
        val observable = rxObservable {
            try {
                Observable.error<String>(RuntimeException("OK")).collect { fail("Should not be here") }
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
