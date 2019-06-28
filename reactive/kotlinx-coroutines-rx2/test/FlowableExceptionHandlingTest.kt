/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import kotlinx.coroutines.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

class FlowableExceptionHandlingTest : TestBase() {

    @Before
    fun setup() {
        ignoreLostThreads("RxComputationThreadPool-", "RxCachedWorkerPoolEvictor-", "RxSchedulerPurge-")
    }

    @Test
    fun testException() = runTest(expected = { it is TestException }) {
        rxFlowable<Int>(Dispatchers.Unconfined) {
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
    fun testFatalException() = runTest(expected = { it is LinkageError }) {
        rxFlowable<Int>(Dispatchers.Unconfined + CoroutineExceptionHandler { _, _ -> expectUnreached() }) {
            expect(1)
            throw LinkageError()
        }.subscribe({
            expectUnreached()
        }, {
            expectUnreached() // Fatal exception is not reported in onError
        })
        finish(2)
    }

    @Test
    fun testExceptionWithoutParent() = runTest {
        GlobalScope.rxFlowable<Int>(Dispatchers.Unconfined + CoroutineExceptionHandler { _, _ -> expectUnreached() }) {
            expect(1)
            throw TestException()
        }.subscribe({
            expectUnreached()
        }, {
            assertTrue(it is TestException)
            expect(2) // Reported to onError
        })
        finish(3)
    }

    @Test
    fun testFatalExceptionWithoutParent() = runTest {
        GlobalScope.rxFlowable<Int>(Dispatchers.Unconfined + CoroutineExceptionHandler { _, e ->
            assertTrue(e is LinkageError); expect(
            2
        )
        }) {
            expect(1)
            throw LinkageError()
        }.subscribe({
            expectUnreached()
        }, {
            expectUnreached() // Fatal exception is not reported in onError
        })
        finish(3)
    }

    @Test
    fun testExceptionAsynchronous() = runTest(expected = { it is TestException }) {
        rxFlowable<Int>(Dispatchers.Unconfined) {
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
    fun testFatalExceptionAsynchronous() = runTest(expected = { it is LinkageError }) {
        rxFlowable<Int>(Dispatchers.Unconfined + CoroutineExceptionHandler { _, _ -> expectUnreached() }) {
            expect(1)
            throw LinkageError()
        }.publish()
            .refCount()
            .subscribe({
                expectUnreached()
            }, {
                expectUnreached() // Fatal exception is not reported in onError
            })
        finish(2)
    }

    @Test
    fun testExceptionAsynchronousWithoutParent() = runTest {
        GlobalScope.rxFlowable<Int>(Dispatchers.Unconfined + CoroutineExceptionHandler { _, _ -> expectUnreached() }) {
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
    fun testFatalExceptionAsynchronousWithoutParent() = runTest {
        GlobalScope.rxFlowable<Int>(Dispatchers.Unconfined + CoroutineExceptionHandler { _, e ->
            assertTrue(e is LinkageError); expect(2)
        }) {
            expect(1)
            throw LinkageError()
        }.publish()
            .refCount()
            .subscribe({
                expectUnreached()
            }, {
                expectUnreached() // Fatal exception is not reported in onError
            })
        finish(3)
    }

    @Test
    fun testFatalExceptionFromSubscribe() = runTest(expected = { it is LinkageError }) {
        rxFlowable(Dispatchers.Unconfined) {
            expect(1)
            send(Unit)
        }.subscribe({
            expect(2)
            throw LinkageError()
        }, { expectUnreached() }) // Unreached because fatal errors are rethrown
        finish(3)
    }

    @Test
    fun testExceptionFromSubscribe() = runTest {
        rxFlowable(Dispatchers.Unconfined) {
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
        rxFlowable(Dispatchers.Unconfined) {
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
    fun testAsynchronousFatalExceptionFromSubscribe() = runTest(expected = { it is LinkageError }) {
        rxFlowable(Dispatchers.Unconfined) {
            expect(1)
            send(Unit)
        }.publish()
            .refCount()
            .subscribe({
                expect(2)
                throw LinkageError()
            }, { expectUnreached() })
        finish(3)
    }

    @Test
    fun testAsynchronousExceptionFromSubscribeWithoutParent() =
        runTest {
            GlobalScope.rxFlowable(Dispatchers.Unconfined) {
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
    fun testAsynchronousFatalExceptionFromSubscribeWithoutParent() =
        runTest {
            GlobalScope.rxFlowable(Dispatchers.Unconfined + CoroutineExceptionHandler { _, e ->
                assertTrue(e is LinkageError); expect(3)
            }) {
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
