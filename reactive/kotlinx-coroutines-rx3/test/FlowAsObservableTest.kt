/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.junit.Test
import kotlin.test.*

class FlowAsObservableTest : TestBase() {
    @Test
    fun testBasicSuccess() = runTest {
        expect(1)
        val observable = flow {
            expect(3)
            emit("OK")
        }.asObservable()

        expect(2)
        observable.subscribe { value ->
            expect(4)
            assertEquals("OK", value)
        }

        finish(5)
    }

    @Test
    fun testBasicFailure() = runTest {
        expect(1)
        val observable = flow<Int> {
            expect(3)
            throw RuntimeException("OK")
        }.asObservable()

        expect(2)
        observable.subscribe({ expectUnreached() }, { error ->
            expect(4)
            assertTrue(error is RuntimeException)
            assertEquals("OK", error.message)
        })
        finish(5)
    }

    @Test
    fun testBasicUnsubscribe() = runTest {
        expect(1)
        val observable = flow<Int> {
            expect(3)
            hang {
                expect(4)
            }
        }.asObservable()

        expect(2)
        val sub = observable.subscribe({ expectUnreached() }, { expectUnreached() })
        sub.dispose() // will cancel coroutine
        finish(5)
    }

    @Test
    fun testNotifyOnceOnCancellation() = runTest {
        val observable =
            flow {
                expect(3)
                emit("OK")
                hang {
                    expect(7)
                }
            }.asObservable()
                .doOnNext {
                    expect(4)
                    assertEquals("OK", it)
                }
                .doOnDispose {
                    expect(6) // notified once!
                }

        expect(1)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            observable.collect {
                expect(5)
                assertEquals("OK", it)
            }
        }

        yield()
        job.cancelAndJoin()
        finish(8)
    }

    @Test
    fun testFailingConsumer() = runTest {
        expect(1)
        val observable = flow {
            expect(2)
            emit("OK")
            hang {
                expect(4)
            }

        }.asObservable()

        try {
            observable.collect {
                expect(3)
                throw TestException()
            }
        } catch (e: TestException) {
            finish(5)
        }
    }

    @Test
    fun testNonAtomicStart() = runTest {
        withContext(Dispatchers.Unconfined) {
            val observable = flow<Int> {
                expect(1)
            }.asObservable()

            val disposable = observable.subscribe({ expectUnreached() }, { expectUnreached() }, { expectUnreached() })
            disposable.dispose()
        }
        finish(2)
    }

    @Test
    fun testFlowCancelledFromWithin() = runTest {
        val observable = flow {
            expect(1)
            emit(1)
            kotlin.coroutines.coroutineContext.cancel()
            kotlin.coroutines.coroutineContext.ensureActive()
            expectUnreached()
        }.asObservable()

        observable.subscribe({ expect(2) }, { expectUnreached() }, { finish(3) })
    }
}
