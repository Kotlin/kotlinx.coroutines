/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import io.reactivex.exceptions.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import java.util.concurrent.*
import kotlin.test.*

class ObservableExceptionHandlingTest : TestBase() {

    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    private inline fun <reified T : Throwable> handler(expect: Int) = { t: Throwable ->
        assertTrue(t is UndeliverableException && t.cause is T, "$t")
        expect(expect)
    }

    private fun cehUnreached() = CoroutineExceptionHandler { _, _ -> expectUnreached() }

    @Test
    fun testException() = withExceptionHandler({ expectUnreached() }) {
        rxObservable<Int>(Dispatchers.Unconfined + cehUnreached()) {
            expect(1)
            throw TestException()
        }.subscribe({
            expectUnreached()
        }, {
            expect(2) // Reported to onError
        })
        finish(3)
    }

    @Test
    fun testFatalException() = withExceptionHandler({ expectUnreached() }) {
        rxObservable<Int>(Dispatchers.Unconfined + cehUnreached()) {
            expect(1)
            throw LinkageError()
        }.subscribe({
            expectUnreached()
        }, {
            expect(2)
        })
        finish(3)
    }

    @Test
    fun testExceptionAsynchronous() = withExceptionHandler({ expectUnreached() }) {
        rxObservable<Int>(Dispatchers.Unconfined) {
            expect(1)
            throw TestException()
        }.publish()
            .refCount()
            .subscribe({
                expectUnreached()
            }, {
                expect(2) // Reported to onError
            })
        finish(3)
    }

    @Test
    fun testFatalExceptionAsynchronous() = withExceptionHandler({ expectUnreached() }) {
        rxObservable<Int>(Dispatchers.Unconfined) {
            expect(1)
            throw LinkageError()
        }.publish()
            .refCount()
            .subscribe({
                expectUnreached()
            }, {
                expect(2) // Fatal exceptions are not treated in a special manner
            })
        finish(3)
    }

    @Test
    fun testFatalExceptionFromSubscribe() = withExceptionHandler(handler<LinkageError>(3)) {
        val latch = CountDownLatch(1)
        rxObservable(Dispatchers.Unconfined) {
            expect(1)
            val result = trySend(Unit)
            val exception = result.exceptionOrNull()
            assertTrue(exception is UndeliverableException)
            assertTrue(exception.cause is LinkageError)
            assertTrue(isClosedForSend)
            expect(4)
            latch.countDown()
        }.subscribe({
            expect(2)
            throw LinkageError()
        }, { expectUnreached() }) // Unreached because RxJava bubbles up fatal exceptions, causing `onNext` to throw.
        latch.await()
        finish(5)
    }

    @Test
    fun testExceptionFromSubscribe() = withExceptionHandler({ expectUnreached() }) {
        rxObservable(Dispatchers.Unconfined) {
            expect(1)
            send(Unit)
        }.subscribe({
            expect(2)
            throw TestException()
        }, { expect(3) })
        finish(4)
    }

    @Test
    fun testAsynchronousExceptionFromSubscribe() = withExceptionHandler({ expectUnreached() }) {
        rxObservable(Dispatchers.Unconfined) {
            expect(1)
            send(Unit)
        }.publish()
            .refCount()
            .subscribe({
                expect(2)
                throw RuntimeException()
            }, { expect(3) })
        finish(4)
    }

    @Test
    fun testAsynchronousFatalExceptionFromSubscribe() = withExceptionHandler(handler<LinkageError>(3)) {
        rxObservable(Dispatchers.Unconfined) {
            expect(1)
            send(Unit)
        }.publish()
            .refCount()
            .subscribe({
                expect(2)
                throw LinkageError()
            }, { expectUnreached() }) // Unreached because RxJava bubbles up fatal exceptions, causing `onNext` to throw.
        finish(4)
    }
}
