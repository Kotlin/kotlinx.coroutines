/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.*
import io.reactivex.functions.*
import io.reactivex.internal.functions.Functions.*
import kotlinx.coroutines.experimental.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

class MaybeTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    @Test
    fun testBasicSuccess() = runBlocking<Unit> {
        expect(1)
        val maybe = rxMaybe(coroutineContext) {
            expect(4)
            "OK"
        }
        expect(2)
        maybe.subscribe { value ->
            expect(5)
            Assert.assertThat(value, IsEqual("OK"))
        }
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicEmpty() = runBlocking<Unit> {
        expect(1)
        val maybe = rxMaybe(coroutineContext) {
            expect(4)
            null
        }
        expect(2)
        maybe.subscribe (emptyConsumer(), ON_ERROR_MISSING, Action {
            expect(5)
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicFailure() = runBlocking<Unit> {
        expect(1)
        val maybe = rxMaybe(coroutineContext) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        maybe.subscribe({
            expectUnreached()
        }, { error ->
            expect(5)
            Assert.assertThat(error, IsInstanceOf(RuntimeException::class.java))
            Assert.assertThat(error.message, IsEqual("OK"))
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }


    @Test
    fun testBasicUnsubscribe() = runBlocking<Unit> {
        expect(1)
        val maybe = rxMaybe(coroutineContext) {
            expect(4)
            yield() // back to main, will get cancelled
            expectUnreached()
        }
        expect(2)
        // nothing is called on a disposed rx2 maybe
        val sub = maybe.subscribe({
            expectUnreached()
        }, {
            expectUnreached()
        })
        expect(3)
        yield() // to started coroutine
        expect(5)
        sub.dispose() // will cancel coroutine
        yield()
        finish(6)
    }

    @Test
    fun testMaybeNoWait() {
        val maybe = rxMaybe(CommonPool) {
            "OK"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMaybeAwait() = runBlocking {
        assertEquals("OK", Maybe.just("O").await() + "K")
    }

    @Test
    fun testMaybeAwaitForNull() = runBlocking {
        assertNull(Maybe.empty<String>().await())
    }

    @Test
    fun testMaybeEmitAndAwait() {
        val maybe = rxMaybe(CommonPool) {
            Maybe.just("O").await() + "K"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMaybeWithDelay() {
        val maybe = rxMaybe(CommonPool) {
            Observable.timer(50, TimeUnit.MILLISECONDS).map { "O" }.awaitSingle() + "K"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMaybeException() {
        val maybe = rxMaybe(CommonPool) {
            Observable.just("O", "K").awaitSingle() + "K"
        }

        checkErroneous(maybe) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val maybe = rxMaybe(CommonPool) {
            Observable.just("O", "#").awaitFirst() + "K"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val maybe = rxMaybe(CommonPool) {
            Observable.just("#", "O").awaitLast() + "K"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val maybe = rxMaybe(CommonPool) {
            try {
                Observable.error<String>(RuntimeException("O")).awaitFirst()
            } catch (e: RuntimeException) {
                Observable.just(e.message!!).awaitLast() + "K"
            }
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromCoroutine() {
        val maybe = rxMaybe<String>(CommonPool) {
            throw IllegalStateException(Observable.just("O").awaitSingle() + "K")
        }

        checkErroneous(maybe) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }
}
