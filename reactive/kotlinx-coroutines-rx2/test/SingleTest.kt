/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx2

import io.reactivex.*
import kotlinx.coroutines.experimental.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import java.util.concurrent.*
import kotlin.coroutines.experimental.*

/**
 * Tests emitting single item with [rxSingle].
 */
class SingleTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    @Test
    fun testBasicSuccess() = runBlocking<Unit> {
        expect(1)
        val single = rxSingle(coroutineContext) {
            expect(4)
            "OK"
        }
        expect(2)
        single.subscribe { value ->
            expect(5)
            Assert.assertThat(value, IsEqual("OK"))
        }
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicFailure() = runBlocking<Unit> {
        expect(1)
        val single = rxSingle(coroutineContext) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        single.subscribe({
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
        val single = rxSingle(coroutineContext) {
            expect(4)
            yield() // back to main, will get cancelled
            expectUnreached()
        }
        expect(2)
        // nothing is called on a disposed rx2 single
        val sub = single.subscribe({
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
    fun testSingleNoWait() {
        val single = rxSingle(CommonPool) {
            "OK"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleAwait() = runBlocking {
        assertEquals("OK", Single.just("O").await() + "K")
    }

    @Test
    fun testSingleEmitAndAwait() {
        val single = rxSingle(CommonPool) {
            Single.just("O").await() + "K"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleWithDelay() {
        val single = rxSingle(CommonPool) {
            Observable.timer(50, TimeUnit.MILLISECONDS).map { "O" }.awaitSingle() + "K"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleException() {
        val single = rxSingle(CommonPool) {
            Observable.just("O", "K").awaitSingle() + "K"
        }

        checkErroneous(single) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val single = rxSingle(CommonPool) {
            Observable.just("O", "#").awaitFirst() + "K"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val single = rxSingle(CommonPool) {
            Observable.just("#", "O").awaitLast() + "K"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val single = rxSingle(CommonPool) {
            try {
                Observable.error<String>(RuntimeException("O")).awaitFirst()
            } catch (e: RuntimeException) {
                Observable.just(e.message!!).awaitLast() + "K"
            }
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromCoroutine() {
        val single = rxSingle<String>(CommonPool) {
            throw IllegalStateException(Observable.just("O").awaitSingle() + "K")
        }

        checkErroneous(single) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }
}
