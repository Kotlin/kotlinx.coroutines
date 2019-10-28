/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.disposables.*
import io.reactivex.functions.*
import kotlinx.coroutines.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*
import java.util.concurrent.*

class SingleTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    @Test
    fun testBasicSuccess() = runBlocking {
        expect(1)
        val single = rxSingle(currentDispatcher()) {
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
        val single = rxSingle(currentDispatcher()) {
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
        val single = rxSingle(currentDispatcher()) {
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
        val single = rxSingle {
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
        val single = rxSingle {
            Single.just("O").await() + "K"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleWithDelay() {
        val single = rxSingle {
            Observable.timer(50, TimeUnit.MILLISECONDS).map { "O" }.awaitSingle() + "K"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testSingleException() {
        val single = rxSingle {
            Observable.just("O", "K").awaitSingle() + "K"
        }

        checkErroneous(single) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val single = rxSingle {
            Observable.just("O", "#").awaitFirst() + "K"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val single = rxSingle {
            Observable.just("#", "O").awaitLast() + "K"
        }

        checkSingleValue(single) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val single = rxSingle {
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
        val single = rxSingle<String> {
            throw IllegalStateException(Observable.just("O").awaitSingle() + "K")
        }

        checkErroneous(single) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }

    @Test
    fun testSuppressedException() = runTest {
        val single = rxSingle(currentDispatcher()) {
            launch(start = CoroutineStart.ATOMIC) {
                throw TestException() // child coroutine fails
            }
            try {
                delay(Long.MAX_VALUE)
            } finally {
                throw TestException2() // but parent throws another exception while cleaning up
            }
        }
        try {
            single.await()
            expectUnreached()
        } catch (e: TestException) {
            assertTrue(e.suppressed[0] is TestException2)
        }
    }

    @Test
    fun testFatalExceptionInSubscribe() = runTest {
        rxSingle(Dispatchers.Unconfined + CoroutineExceptionHandler { _, e -> assertTrue(e is LinkageError); expect(2) }) {
            expect(1)
            42
        }.subscribe(Consumer {
            throw LinkageError()
        })
        finish(3)
    }

    @Test
    fun testFatalExceptionInSingle() = runTest {
        rxSingle(Dispatchers.Unconfined) {
            throw LinkageError()
        }.subscribe({ _, e ->  assertTrue(e is LinkageError); expect(1) })

        finish(2)
    }

    @Test
    fun testUnhandledException() = runTest {
        expect(1)
        var disposable: Disposable? = null
        val eh = CoroutineExceptionHandler { _, t ->
            assertTrue(t is TestException)
            expect(5)
        }
        val single = rxSingle(currentDispatcher() + eh) {
            expect(4)
            disposable!!.dispose() // cancel our own subscription, so that delay will get cancelled
            try {
                delay(Long.MAX_VALUE)
            } finally {
                throw TestException() // would not be able to handle it since mono is disposed
            }
        }
        single.subscribe(object : SingleObserver<Unit> {
            override fun onSubscribe(d: Disposable) {
                expect(2)
                disposable = d
            }
            override fun onSuccess(t: Unit) { expectUnreached() }
            override fun onError(t: Throwable) { expectUnreached() }
        })
        expect(3)
        yield() // run coroutine
        finish(6)
    }
}
