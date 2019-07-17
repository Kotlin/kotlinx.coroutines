/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class ObservableExceptionHandlingTest : TestBase() {

    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    private inline fun <reified T : Throwable> ceh(expect: Int) = CoroutineExceptionHandler { _, t ->
        assertTrue(t is T)
        expect(expect)
    }

    private fun cehUnreached() = CoroutineExceptionHandler { _, _ -> expectUnreached() }

    @Test
    fun testException() = runTest {
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
    fun testFatalException() = runTest {
        rxObservable<Int>(Dispatchers.Unconfined + ceh<LinkageError>(3)) {
            expect(1)
            throw LinkageError()
        }.subscribe({
            expectUnreached()
        }, {
            expect(2)
        })
        finish(4)
    }

    @Test
    fun testExceptionAsynchronous() = runTest {
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
    fun testFatalExceptionAsynchronous() = runTest {
        rxObservable<Int>(Dispatchers.Unconfined + ceh<LinkageError>(3)) {
            expect(1)
            throw LinkageError()
        }.publish()
            .refCount()
            .subscribe({
                expectUnreached()
            }, {
                expect(2) // Fatal exception is not reported in onError
            })
        finish(4)
    }

    @Test
    fun testFatalExceptionFromSubscribe() = runTest {
        rxObservable(Dispatchers.Unconfined + ceh<LinkageError>(4)) {
            expect(1)
            send(Unit)
        }.subscribe({
            expect(2)
            throw LinkageError()
        }, { expect(3) }) // Unreached because fatal errors are rethrown
        finish(5)
    }

    @Test
    fun testExceptionFromSubscribe() = runTest {
        rxObservable(Dispatchers.Unconfined) {
            expect(1)
            send(Unit)
        }.subscribe({
            expect(2)
            throw TestException()
        }, { expect(3) }) // not reported to onError because came from the subscribe itself
        finish(4)
    }

    @Test
    fun testAsynchronousExceptionFromSubscribe() = runTest {
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
    fun testAsynchronousFatalExceptionFromSubscribe() = runTest {
        rxObservable(Dispatchers.Unconfined + ceh<LinkageError>(4)) {
            expect(1)
            send(Unit)
        }.publish()
            .refCount()
            .subscribe({
                expect(2)
                throw LinkageError()
            }, { expect(3) })
        finish(5)
    }
}
