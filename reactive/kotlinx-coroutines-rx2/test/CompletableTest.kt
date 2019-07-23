/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.disposables.*
import kotlinx.coroutines.*
import org.hamcrest.core.*
import org.junit.*
import org.junit.Assert.*

class CompletableTest : TestBase() {
    @Test
    fun testBasicSuccess() = runBlocking {
        expect(1)
        val completable = rxCompletable(currentDispatcher()) {
            expect(4)
        }
        expect(2)
        completable.subscribe {
            expect(5)
        }
        expect(3)
        yield() // to completable coroutine
        finish(6)
    }

    @Test
    fun testBasicFailure() = runBlocking {
        expect(1)
        val completable = rxCompletable(currentDispatcher()) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        completable.subscribe({
            expectUnreached()
        }, { error ->
            expect(5)
            assertThat(error, IsInstanceOf(RuntimeException::class.java))
            assertThat(error.message, IsEqual("OK"))
        })
        expect(3)
        yield() // to completable coroutine
        finish(6)
    }

    @Test
    fun testBasicUnsubscribe() = runBlocking {
        expect(1)
        val completable = rxCompletable(currentDispatcher()) {
            expect(4)
            yield() // back to main, will get cancelled
            expectUnreached()
        }
        expect(2)
        // nothing is called on a disposed rx2 completable
        val sub = completable.subscribe({
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
    fun testAwaitSuccess() = runBlocking {
        expect(1)
        val completable = rxCompletable(currentDispatcher()) {
            expect(3)
        }
        expect(2)
        completable.await() // shall launch coroutine
        finish(4)
    }

    @Test
    fun testAwaitFailure() = runBlocking {
        expect(1)
        val completable = rxCompletable(currentDispatcher()) {
            expect(3)
            throw RuntimeException("OK")
        }
        expect(2)
        try {
            completable.await() // shall launch coroutine and throw exception
            expectUnreached()
        } catch (e: RuntimeException) {
            finish(4)
            assertThat(e.message, IsEqual("OK"))
        }
    }

    @Test
    fun testSuppressedException() = runTest {
        val completable = rxCompletable(currentDispatcher()) {
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
            completable.await()
            expectUnreached()
        } catch (e: TestException) {
            assertTrue(e.suppressed[0] is TestException2)
        }
    }

    @Test
    fun testUnhandledException() = runTest() {
        expect(1)
        var disposable: Disposable? = null
        val eh = CoroutineExceptionHandler { _, t ->
            assertTrue(t is TestException)
            expect(5)
        }
        val completable = rxCompletable(currentDispatcher() + eh) {
            expect(4)
            disposable!!.dispose() // cancel our own subscription, so that delay will get cancelled
            try {
                delay(Long.MAX_VALUE)
            } finally {
                throw TestException() // would not be able to handle it since mono is disposed
            }
        }
        completable.subscribe(object : CompletableObserver {
            override fun onSubscribe(d: Disposable) {
                expect(2)
                disposable = d
            }
            override fun onComplete() { expectUnreached() }
            override fun onError(t: Throwable) { expectUnreached() }
        })
        expect(3)
        yield() // run coroutine
        finish(6)
    }

    @Test
    fun testFatalExceptionInSubscribe() = runTest {
        GlobalScope.rxCompletable(Dispatchers.Unconfined + CoroutineExceptionHandler{ _, e -> assertTrue(e is LinkageError); expect(2)}) {
            expect(1)
            42
        }.subscribe({ throw LinkageError() })
        finish(3)
    }

    @Test
    fun testFatalExceptionInSingle() = runTest {
        GlobalScope.rxCompletable(Dispatchers.Unconfined) {
            throw LinkageError()
        }.subscribe({ expectUnreached()  }, { expect(1); assertTrue(it is LinkageError) })
        finish(2)
    }
}
