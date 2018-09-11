/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx1

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.CancellationException
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import rx.*
import java.util.concurrent.*

class SingleTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxComputationScheduler-", "RxIoScheduler-")
    }

    @Test
    fun testBasicSuccess() = runBlocking {
        expect(1)
        val single = rxSingle {
            expect(4)
            "OK"
        }
        expect(2)
        single.subscribe { value ->
            expect(5)
            assertThat(value, IsEqual("OK"))
        }
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicFailure() = runBlocking {
        expect(1)
        val single = rxSingle {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        single.subscribe({
            expectUnreached()
        }, { error ->
            expect(5)
            assertThat(error, IsInstanceOf(RuntimeException::class.java))
            assertThat(error.message, IsEqual("OK"))
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }


    @Test
    fun testBasicUnsubscribe() = runBlocking {
        expect(1)
        val single = rxSingle {
            expect(4)
            yield() // back to main, will get cancelled
            expectUnreached()
        }
        expect(2)
        val sub = single.subscribe({
            expectUnreached()
        }, { error ->
            expect(6)
            assertThat(error, IsInstanceOf(CancellationException::class.java))
        })
        expect(3)
        yield() // to started coroutine
        expect(5)
        sub.unsubscribe() // will cancel coroutine
        yield()
        finish(7)
    }

    @Test
    fun testSingleNoWait() {
        val single = GlobalScope.rxSingle {
            "OK"
        }

        checkSingleValue(single) {
            assertThat(it, IsEqual("OK"))
        }
    }

    @Test
    fun testSingleNullNoWait() {
        val single = GlobalScope.rxSingle<String?> {
            null
        }

        checkSingleValue(single) {
            assertThat(it, IsNull())
        }
    }

    @Test
    fun testSingleAwait() = runBlocking {
        assertEquals("OK", Single.just("O").await() + "K")
    }

    @Test
    fun testSingleEmitAndAwait() {
        val single = GlobalScope.rxSingle {
            Single.just("O").await() + "K"
        }

        checkSingleValue(single) {
            assertThat(it, IsEqual("OK"))
        }
    }

    @Test
    fun testSingleWithDelay() {
        val single = GlobalScope.rxSingle {
            Observable.timer(50, TimeUnit.MILLISECONDS).map { "O" }.awaitSingle() + "K"
        }

        checkSingleValue(single) {
            assertThat(it, IsEqual("OK"))
        }
    }

    @Test
    fun testSingleException() {
        val single = GlobalScope.rxSingle {
            Observable.just("O", "K").awaitSingle() + "K"
        }

        checkErroneous(single) {
            assertThat(it, IsInstanceOf(IllegalArgumentException::class.java))
        }
    }

    @Test
    fun testAwaitFirst() {
        val single = GlobalScope.rxSingle {
            Observable.just("O", "#").awaitFirst() + "K"
        }

        checkSingleValue(single) {
            assertThat(it, IsEqual("OK"))
        }
    }

    @Test
    fun testAwaitLast() {
        val single = GlobalScope.rxSingle {
            Observable.just("#", "O").awaitLast() + "K"
        }

        checkSingleValue(single) {
            assertThat(it, IsEqual("OK"))
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val single = GlobalScope.rxSingle {
            try {
                Observable.error<String>(RuntimeException("O")).awaitFirst()
            } catch (e: RuntimeException) {
                Observable.just(e.message!!).awaitLast() + "K"
            }
        }

        checkSingleValue(single) {
            assertThat(it, IsEqual("OK"))
        }
    }

    @Test
    fun testExceptionFromCoroutine() {
        val single = GlobalScope.rxSingle<String> {
            throw RuntimeException(Observable.just("O").awaitSingle() + "K")
        }

        checkErroneous(single) {
            assertThat(it, IsInstanceOf(RuntimeException::class.java))
            assertEquals("OK", it.message)
        }
    }
}
