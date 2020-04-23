/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import io.reactivex.rxjava3.core.*
import io.reactivex.rxjava3.plugins.*
import kotlinx.coroutines.*
import kotlinx.coroutines.CancellationException
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class ObservableTest : TestBase() {
    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    @Test
    fun testBasicSuccess() = runBlocking {
        expect(1)
        val observable = rxObservable(currentDispatcher()) {
            expect(4)
            send("OK")
        }
        expect(2)
        observable.subscribe { value ->
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
        val observable = rxObservable<String>(currentDispatcher()) {
            expect(4)
            throw RuntimeException("OK")
        }
        expect(2)
        observable.subscribe({
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
        val observable = rxObservable<String>(currentDispatcher()) {
            expect(4)
            yield() // back to main, will get cancelled
            expectUnreached()
        }
        expect(2)
        val sub = observable.subscribe({
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
    fun testNotifyOnceOnCancellation() = runTest {
        expect(1)
        val observable =
            rxObservable(currentDispatcher()) {
                expect(5)
                send("OK")
                try {
                    delay(Long.MAX_VALUE)
                } catch (e: CancellationException) {
                    expect(11)
                }
            }
            .doOnNext {
                expect(6)
                assertEquals("OK", it)
            }
            .doOnDispose {
                expect(10) // notified once!
            }
        expect(2)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(3)
            observable.collect {
                expect(8)
                assertEquals("OK", it)
            }
        }
        expect(4)
        yield() // to observable code
        expect(7)
        yield() // to consuming coroutines
        expect(9)
        job.cancel()
        job.join()
        finish(12)
    }

    @Test
    fun testFailingConsumer() = runTest {
        expect(1)
        val pub = rxObservable(currentDispatcher()) {
            expect(2)
            send("OK")
            try {
                delay(Long.MAX_VALUE)
            } catch (e: CancellationException) {
                finish(5)
            }
        }
        try {
            pub.collect {
                expect(3)
                throw TestException()
            }
        } catch (e: TestException) {
            expect(4)
        }
    }

    @Test
    fun testExceptionAfterCancellation() {
        // Test that no exceptions were reported to the global EH (it will fail the test if so)
        val handler = { e: Throwable ->
            assertFalse(e is CancellationException)
        }
        withExceptionHandler(handler) {
            RxJavaPlugins.setErrorHandler {
                require(it !is CancellationException)
            }
            Observable
                .interval(1, TimeUnit.MILLISECONDS)
                .take(1000)
                .switchMapSingle {
                    rxSingle {
                        timeBomb().await()
                    }
                }
                .blockingSubscribe({}, {})
        }
    }

    private fun timeBomb() = Single.timer(1, TimeUnit.MILLISECONDS).doOnSuccess { throw TestException() }
}
