/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.*
import io.reactivex.disposables.*
import io.reactivex.exceptions.*
import io.reactivex.internal.functions.Functions.*
import kotlinx.coroutines.*
import kotlinx.coroutines.CancellationException
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class MaybeTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    @Test
    fun testBasicSuccess() = runBlocking {
        expect(1)
        val maybe = rxMaybe(currentDispatcher()) {
            expect(4)
            "OK"
        }
        expect(2)
        maybe.subscribe { value ->
            expect(5)
            assertEquals("OK", value)
        }
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicEmpty() = runBlocking {
        expect(1)
        val maybe = rxMaybe(currentDispatcher()) {
            expect(4)
            null
        }
        expect(2)
        maybe.subscribe (emptyConsumer(), ON_ERROR_MISSING, {
            expect(5)
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }

    @Test
    fun testBasicFailure() = runBlocking {
        expect(1)
        val maybe = rxMaybe(currentDispatcher()) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        maybe.subscribe({
            expectUnreached()
        }, { error ->
            expect(5)
            assertTrue(error is RuntimeException)
            assertEquals("OK", error.message)
        })
        expect(3)
        yield() // to started coroutine
        finish(6)
    }


    @Test
    fun testBasicUnsubscribe() = runBlocking {
        expect(1)
        val maybe = rxMaybe(currentDispatcher()) {
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
        val maybe = rxMaybe {
            "OK"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMaybeAwait() = runBlocking {
        assertEquals("OK", Maybe.just("O").awaitSingleOrNull() + "K")
        assertEquals("OK", Maybe.just("O").awaitSingle() + "K")
    }

    @Test
    fun testMaybeAwaitForNull(): Unit = runBlocking {
        assertNull(Maybe.empty<String>().awaitSingleOrNull())
        assertFailsWith<NoSuchElementException> { Maybe.empty<String>().awaitSingle() }
    }

    /** Tests that calls to [awaitSingleOrNull] throw [CancellationException] and dispose of the subscription when their
     * [Job] is cancelled. */
    @Test
    fun testMaybeAwaitCancellation() = runTest {
        expect(1)
        val maybe = MaybeSource<Int> { s ->
            s.onSubscribe(object: Disposable {
                override fun dispose() { expect(4) }
                override fun isDisposed(): Boolean { expectUnreached(); return false }
            })
        }
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            try {
                expect(2)
                maybe.awaitSingleOrNull()
            } catch (e: CancellationException) {
                expect(5)
                throw e
            }
        }
        expect(3)
        job.cancelAndJoin()
        finish(6)
    }

    @Test
    fun testMaybeEmitAndAwait() {
        val maybe = rxMaybe {
            Maybe.just("O").awaitSingleOrNull() + "K"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMaybeWithDelay() {
        val maybe = rxMaybe {
            Observable.timer(50, TimeUnit.MILLISECONDS).map { "O" }.awaitSingle() + "K"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testMaybeException() {
        val maybe = rxMaybe {
            Observable.just("O", "K").awaitSingle() + "K"
        }

        checkErroneous(maybe) {
            assert(it is IllegalArgumentException)
        }
    }

    @Test
    fun testAwaitFirst() {
        val maybe = rxMaybe {
            Observable.just("O", "#").awaitFirst() + "K"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testAwaitLast() {
        val maybe = rxMaybe {
            Observable.just("#", "O").awaitLast() + "K"
        }

        checkMaybeValue(maybe) {
            assertEquals("OK", it)
        }
    }

    @Test
    fun testExceptionFromObservable() {
        val maybe = rxMaybe {
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
        val maybe = rxMaybe<String> {
            throw IllegalStateException(Observable.just("O").awaitSingle() + "K")
        }

        checkErroneous(maybe) {
            assert(it is IllegalStateException)
            assertEquals("OK", it.message)
        }
    }

    @Test
    fun testCancelledConsumer() = runTest {
        expect(1)
        val maybe = rxMaybe(currentDispatcher()) {
            expect(4)
            try {
                delay(Long.MAX_VALUE)
            } catch (e: CancellationException) {
                expect(6)
            }
            42
        }
        expect(2)
        val timeout = withTimeoutOrNull(100) {
            expect(3)
            maybe.collect {
                expectUnreached()
            }
            expectUnreached()
        }
        assertNull(timeout)
        expect(5)
        yield() // must cancel code inside maybe!!!
        finish(7)
    }

    /** Tests the simple scenario where the Maybe doesn't output a value. */
    @Test
    fun testMaybeCollectEmpty() = runTest {
        expect(1)
        Maybe.empty<Int>().collect {
            expectUnreached()
        }
        finish(2)
    }

    /** Tests the simple scenario where the Maybe doesn't output a value. */
    @Test
    fun testMaybeCollectSingle() = runTest {
        expect(1)
        Maybe.just("OK").collect {
            assertEquals("OK", it)
            expect(2)
        }
        finish(3)
    }

    /** Tests the behavior of [collect] when the Maybe raises an error. */
    @Test
    fun testMaybeCollectThrowingMaybe() = runTest {
        expect(1)
        try {
            Maybe.error<Int>(TestException()).collect {
                expectUnreached()
            }
        } catch (e: TestException) {
            expect(2)
        }
        finish(3)
    }

    /** Tests the behavior of [collect] when the action throws. */
    @Test
    fun testMaybeCollectThrowingAction() = runTest {
        expect(1)
        try {
            Maybe.just("OK").collect {
                expect(2)
                throw TestException()
            }
        } catch (e: TestException) {
            expect(3)
        }
        finish(4)
    }

    @Test
    fun testSuppressedException() = runTest {
        val maybe = rxMaybe(currentDispatcher()) {
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
            maybe.awaitSingleOrNull()
            expectUnreached()
        } catch (e: TestException) {
            assertTrue(e.suppressed[0] is TestException2)
        }
    }

    @Test
    fun testUnhandledException() = runTest {
        expect(1)
        var disposable: Disposable? = null
        val handler = { e: Throwable ->
            assertTrue(e is UndeliverableException && e.cause is TestException)
            expect(5)
        }
        val maybe = rxMaybe(currentDispatcher()) {
            expect(4)
            disposable!!.dispose() // cancel our own subscription, so that delay will get cancelled
            try {
                delay(Long.MAX_VALUE)
            } finally {
                throw TestException() // would not be able to handle it since mono is disposed
            }
        }
        withExceptionHandler(handler) {
            maybe.subscribe(object : MaybeObserver<Unit> {
                override fun onSubscribe(d: Disposable) {
                    expect(2)
                    disposable = d
                }

                override fun onComplete() {
                    expectUnreached()
                }

                override fun onSuccess(t: Unit) {
                    expectUnreached()
                }

                override fun onError(t: Throwable) {
                    expectUnreached()
                }
            })
            expect(3)
            yield() // run coroutine
            finish(6)
        }
    }

    @Test
    fun testFatalExceptionInSubscribe() = runTest {
        val handler = { e: Throwable ->
            assertTrue(e is UndeliverableException && e.cause is LinkageError)
            expect(2)
        }

        withExceptionHandler(handler) {
            rxMaybe(Dispatchers.Unconfined) {
                expect(1)
                42
            }.subscribe { throw LinkageError() }
            finish(3)
        }
    }

    @Test
    fun testFatalExceptionInSingle() = runTest {
        rxMaybe(Dispatchers.Unconfined) {
            throw LinkageError()
        }.subscribe({ expectUnreached()  }, { expect(1); assertTrue(it is LinkageError) })
        finish(2)
    }
}
