package kotlinx.coroutines.rx3

import kotlinx.coroutines.testing.*
import io.reactivex.rxjava3.core.*
import io.reactivex.rxjava3.disposables.*
import io.reactivex.rxjava3.exceptions.*
import io.reactivex.rxjava3.functions.*
import kotlinx.coroutines.*
import kotlinx.coroutines.CancellationException
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

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
            assertEquals("OK", value)
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
            assertIs<RuntimeException>(error)
            assertEquals("OK", error.message)
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
        // nothing is called on a disposed rx3 single
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

    /** Tests that calls to [await] throw [CancellationException] and dispose of the subscription when their
     * [Job] is cancelled. */
    @Test
    fun testSingleAwaitCancellation() = runTest {
        expect(1)
        val single = SingleSource<Int> { s ->
            s.onSubscribe(object: Disposable {
                override fun dispose() { expect(4) }
                override fun isDisposed(): Boolean { expectUnreached(); return false }
            })
        }
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            try {
                expect(2)
                single.await()
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
            assertIs<TestException2>(e.suppressed[0])
        }
    }

    @Test
    fun testFatalExceptionInSubscribe() = runTest {
        val handler = { e: Throwable ->
            assertTrue(e is UndeliverableException && e.cause is LinkageError)
            expect(2)
        }
        withExceptionHandler(handler) {
            rxSingle(Dispatchers.Unconfined) {
                expect(1)
                42
            }.subscribe(Consumer {
                throw LinkageError()
            })
            finish(3)
        }
    }

    @Test
    fun testFatalExceptionInSingle() = runTest {
        rxSingle(Dispatchers.Unconfined) {
            throw LinkageError()
        }.subscribe { _, e -> assertIs<LinkageError>(e); expect(1) }

        finish(2)
    }

    @Test
    fun testUnhandledException() = runTest {
        expect(1)
        var disposable: Disposable? = null
        val handler = { e: Throwable ->
            assertTrue(e is UndeliverableException && e.cause is TestException)
            expect(5)
        }
        val single = rxSingle(currentDispatcher()) {
            expect(4)
            disposable!!.dispose() // cancel our own subscription, so that delay will get cancelled
            try {
                delay(Long.MAX_VALUE)
            } finally {
                throw TestException() // would not be able to handle it since mono is disposed
            }
        }
        withExceptionHandler(handler) {
            single.subscribe(object : SingleObserver<Unit> {
                override fun onSubscribe(d: Disposable) {
                    expect(2)
                    disposable = d
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
}
