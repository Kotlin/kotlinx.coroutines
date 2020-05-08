/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import io.reactivex.rxjava3.exceptions.*
import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class FlowableExceptionHandlingTest : TestBase() {

    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    private inline fun <reified T : Throwable> handler(expect: Int) = { t: Throwable ->
        assertTrue(t is UndeliverableException && t.cause is T)
        expect(expect)
    }

    private fun cehUnreached() = CoroutineExceptionHandler { _, _ -> expectUnreached() }

    @Test
    fun testException() = withExceptionHandler({ expectUnreached() }) {
        rxFlowable<Int>(Dispatchers.Unconfined + cehUnreached()) {
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
    fun testFatalException() = withExceptionHandler(handler<LinkageError>(3)) {
        rxFlowable<Int>(Dispatchers.Unconfined) {
            expect(1)
            throw LinkageError()
        }.subscribe({
            expectUnreached()
        }, {
            expect(2) // Fatal exception is reported to both onError and CEH
        })
        finish(4)
    }

    @Test
    fun testExceptionAsynchronous() = withExceptionHandler({ expectUnreached() }) {
        rxFlowable<Int>(Dispatchers.Unconfined + cehUnreached()) {
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
    fun testFatalExceptionAsynchronous() = withExceptionHandler(handler<LinkageError>(3)) {
        rxFlowable<Int>(Dispatchers.Unconfined) {
            expect(1)
            throw LinkageError()
        }.publish()
            .refCount()
            .subscribe({
                expectUnreached()
            }, {
                expect(2)
            })
        finish(4)
    }

    @Test
    fun testFatalExceptionFromSubscribe() = withExceptionHandler(handler<LinkageError>(4)) {
        rxFlowable(Dispatchers.Unconfined) {
            expect(1)
            send(Unit)
        }.subscribe({
            expect(2)
            throw LinkageError()
        }, { expect(3) }) // Fatal exception is reported to both onError and CEH
        finish(5)
    }

    @Test
    fun testExceptionFromSubscribe() = withExceptionHandler({ expectUnreached() }) {
        rxFlowable(Dispatchers.Unconfined + cehUnreached()) {
            expect(1)
            send(Unit)
        }.subscribe({
            expect(2)
            throw TestException()
        }, { expect(3) }) // not reported to onError because came from the subscribe itself
        finish(4)
    }

    @Test
    fun testAsynchronousExceptionFromSubscribe() = withExceptionHandler({ expectUnreached() }) {
        rxFlowable(Dispatchers.Unconfined + cehUnreached()) {
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
        rxFlowable(Dispatchers.Unconfined) {
            expect(1)
            send(Unit)
        }.publish()
            .refCount()
            .subscribe({
                expect(2)
                throw LinkageError()
            }, { expectUnreached() })
        finish(4)
    }
}
