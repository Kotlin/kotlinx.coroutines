/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.*
import org.junit.Assert.*

class ConvertTest : TestBase() {
    class TestException(s: String): RuntimeException(s)

    @Test
    fun testToCompletableSuccess() = runBlocking {
        expect(1)
        val job = launch {
            expect(3)
        }
        val completable = job.asCompletable(coroutineContext)
        completable.subscribe {
            expect(4)
        }
        expect(2)
        yield()
        finish(5)
    }

    @Test
    fun testToCompletableFail() = runBlocking {
        expect(1)
        val job = async(NonCancellable) { // don't kill parent on exception
            expect(3)
            throw RuntimeException("OK")
        }
        val completable = job.asCompletable(coroutineContext)
        completable.subscribe {
            expect(4)
        }
        expect(2)
        yield()
        finish(5)
    }

    @Test
    fun testToMaybe() {
        val d = GlobalScope.async {
            delay(50)
            "OK"
        }
        val maybe1 = d.asMaybe(Dispatchers.Unconfined)
        checkMaybeValue(maybe1) {
            assertEquals("OK", it)
        }
        val maybe2 = d.asMaybe(Dispatchers.Unconfined)
        checkMaybeValue(maybe2) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testToMaybeEmpty() {
        val d = GlobalScope.async {
            delay(50)
            null
        }
        val maybe1 = d.asMaybe(Dispatchers.Unconfined)
        checkMaybeValue(maybe1, ::assertNull)
        val maybe2 = d.asMaybe(Dispatchers.Unconfined)
        checkMaybeValue(maybe2, ::assertNull)
    }

    @Test
    fun testToMaybeFail() {
        val d = GlobalScope.async {
            delay(50)
            throw TestException("OK")
        }
        val maybe1 = d.asMaybe(Dispatchers.Unconfined)
        checkErroneous(maybe1) {
            check(it is TestException && it.message == "OK") { "$it" }
        }
        val maybe2 = d.asMaybe(Dispatchers.Unconfined)
        checkErroneous(maybe2) {
            check(it is TestException && it.message == "OK") { "$it" }
        }
    }

    @Test
    fun testToSingle() {
        val d = GlobalScope.async {
            delay(50)
            "OK"
        }
        val single1 = d.asSingle(Dispatchers.Unconfined)
        checkSingleValue(single1) {
            assertEquals("OK", it)
        }
        val single2 = d.asSingle(Dispatchers.Unconfined)
        checkSingleValue(single2) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testToSingleFail() {
        val d = GlobalScope.async {
            delay(50)
            throw TestException("OK")
        }
        val single1 = d.asSingle(Dispatchers.Unconfined)
        checkErroneous(single1) {
            check(it is TestException && it.message == "OK") { "$it" }
        }
        val single2 = d.asSingle(Dispatchers.Unconfined)
        checkErroneous(single2) {
            check(it is TestException && it.message == "OK") { "$it" }
        }
    }

    @Test
    fun testToObservable() {
        val c = GlobalScope.produce {
            delay(50)
            send("O")
            delay(50)
            send("K")
        }
        val observable = c.asObservable(Dispatchers.Unconfined)
        checkSingleValue(observable.reduce { t1, t2 -> t1 + t2 }.toSingle()) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testToObservableFail() {
        val c = GlobalScope.produce {
            delay(50)
            send("O")
            delay(50)
            throw TestException("K")
        }
        val observable = c.asObservable(Dispatchers.Unconfined)
        val single = GlobalScope.rxSingle(Dispatchers.Unconfined) {
            var result = ""
            try {
                observable.consumeEach { result += it }
            } catch(e: Throwable) {
                check(e is TestException)
                result += e.message
            }
            result
        }
        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }
}