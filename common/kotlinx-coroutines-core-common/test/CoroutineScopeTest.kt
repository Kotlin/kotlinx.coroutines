/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("UNREACHABLE_CODE")

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.test.*

class CoroutineScopeTest : TestBase() {
    @Test
    fun testScope() = runTest {
        suspend fun callJobScoped() = coroutineScope {
            expect(2)
            launch {
                expect(4)
            }
            launch {
                expect(5)

                launch {
                    expect(7)
                }

                expect(6)

            }
            expect(3)
            42
        }
        expect(1)
        val result = callJobScoped()
        assertEquals(42, result)
        yield() // Check we're not cancelled
        finish(8)
    }

    @Test
    fun testScopeCancelledFromWithin() = runTest {
        expect(1)
        suspend fun callJobScoped() = coroutineScope {
            launch {
                expect(2)
                delay(Long.MAX_VALUE)
            }
            launch {
                expect(3)
                throw TestException2()
            }
        }

        try {
            callJobScoped()
            expectUnreached()
        } catch (e: TestException2) {
            expect(4)
        }
        yield() // Check we're not cancelled
        finish(5)
    }

    @Test
    fun testExceptionFromWithin() = runTest {
        expect(1)
        try {
            expect(2)
            coroutineScope {
                expect(3)
                throw TestException1()
            }
            expectUnreached()
        } catch (e: TestException1) {
            finish(4)
        }
    }

    @Test
    fun testScopeBlockThrows() = runTest {
        expect(1)
        suspend fun callJobScoped(): Unit = coroutineScope {
            launch {
                expect(2)
                delay(Long.MAX_VALUE)
            }
            yield() // let launch sleep
            throw TestException1()
        }
        try {
            callJobScoped()
            expectUnreached()
        } catch (e: TestException1) {
            expect(3)
        }
        yield() // Check we're not cancelled
        finish(4)
    }

    @Test
    fun testOuterJobIsCancelled() = runTest {
        suspend fun callJobScoped() = coroutineScope {
            launch {
                expect(3)
                try {
                    delay(Long.MAX_VALUE)
                } finally {
                    expect(4)
                }
            }

            expect(2)
            delay(Long.MAX_VALUE)
            42
        }

        val outerJob = launch(NonCancellable) {
            expect(1)
            try {
                callJobScoped()
                expectUnreached()
            } catch (e: CancellationException) {
                expect(5)
                assertNull(e.cause)
            }
        }
        repeat(3) { yield() } // let everything to start properly
        outerJob.cancel()
        outerJob.join()
        finish(6)
    }

    @Test
    fun testAsyncCancellationFirst() = runTest {
        try {
            expect(1)
            failedConcurrentSumFirst()
            expectUnreached()
        } catch (e: TestException1) {
            finish(6)
        }
    }

    // First async child fails -> second is cancelled
    private suspend fun failedConcurrentSumFirst(): Int = coroutineScope {
        val one = async<Int> {
            expect(3)
            throw TestException1()
        }
        val two = async(start = CoroutineStart.ATOMIC) {
            try {
                expect(4)
                delay(Long.MAX_VALUE) // Emulates very long computation
                42
            } finally {
                expect(5)
            }
        }
        expect(2)
        one.await() + two.await()
    }

    @Test
    fun testAsyncCancellationSecond() = runTest {
        try {
            expect(1)
            failedConcurrentSumSecond()
            expectUnreached()
        } catch (e: TestException1) {
            finish(6)
        }
    }

    // Second async child fails -> fist is cancelled
    private suspend fun failedConcurrentSumSecond(): Int = coroutineScope {
        val one = async<Int> {
            try {
                expect(3)
                delay(Long.MAX_VALUE) // Emulates very long computation
                42
            } finally {
                expect(5)
            }
        }
        val two = async<Int>(start = CoroutineStart.ATOMIC) {
            expect(4)
            throw TestException1()
        }
        expect(2)
        one.await() + two.await()
    }

    @Test
    @Suppress("UNREACHABLE_CODE")
    fun testDocumentationExample() = runTest {
        suspend fun loadData() = coroutineScope {
            expect(1)
            val data = async {
                try {
                    delay(Long.MAX_VALUE)
                } finally {
                    expect(3)
                }
            }
            yield()
            // UI updater
            withContext(coroutineContext) {
                expect(2)
                throw TestException1()
                data.await() // Actually unreached
                expectUnreached()
            }
        }

        try {
            loadData()
            expectUnreached()
        } catch (e: TestException1) {
            finish(4)
        }
    }

    @Test
    fun testCoroutineScopeCancellationVsException() = runTest {
        expect(1)
        var job: Job? = null
        job = launch(start = CoroutineStart.UNDISPATCHED) {
            expect(2)
            try {
                coroutineScope {
                    expect(3)
                    yield() // must suspend
                    expect(5)
                    job!!.cancel() // cancel this job _before_ it throws
                    throw TestException1()
                }
            } catch (e: TestException1) {
                // must have caught TextException
                expect(6)
            }
        }
        expect(4)
        yield() // to coroutineScope
        finish(7)
    }

    @Test
    fun testScopePlusContext() {
        assertSame(EmptyCoroutineContext, scopePlusContext(EmptyCoroutineContext, EmptyCoroutineContext))
        assertSame(Dispatchers.Default, scopePlusContext(EmptyCoroutineContext, Dispatchers.Default))
        assertSame(Dispatchers.Default, scopePlusContext(Dispatchers.Default, EmptyCoroutineContext))
        assertSame(Dispatchers.Default, scopePlusContext(Dispatchers.Default, Dispatchers.Default))
        assertSame(Dispatchers.Default, scopePlusContext(Dispatchers.Unconfined, Dispatchers.Default))
        assertSame(Dispatchers.Unconfined, scopePlusContext(Dispatchers.Default, Dispatchers.Unconfined))
        assertSame(Dispatchers.Unconfined, scopePlusContext(Dispatchers.Unconfined, Dispatchers.Unconfined))
    }

    @Test
    fun testIncompleteScopeState() = runTest {
        lateinit var scopeJob: Job
        coroutineScope {
            scopeJob = coroutineContext[Job]!!
            scopeJob.invokeOnCompletion { }
        }

        scopeJob.join()
        assertTrue(scopeJob.isCompleted)
        assertFalse(scopeJob.isActive)
        assertFalse(scopeJob.isCancelled)
    }

    @Test
    fun testRestartableScopePlusContext() {
        assertSame(EmptyCoroutineContext, restartableScopePlusContext(EmptyCoroutineContext, EmptyCoroutineContext))
        assertSame(Dispatchers.Default, restartableScopePlusContext(EmptyCoroutineContext, Dispatchers.Default))
        assertSame(Dispatchers.Default, restartableScopePlusContext(Dispatchers.Default, EmptyCoroutineContext))
        assertSame(Dispatchers.Default, restartableScopePlusContext(Dispatchers.Default, Dispatchers.Default))
        assertSame(Dispatchers.Default, restartableScopePlusContext(Dispatchers.Unconfined, Dispatchers.Default))
        assertSame(Dispatchers.Unconfined, restartableScopePlusContext(Dispatchers.Default, Dispatchers.Unconfined))
        assertSame(Dispatchers.Unconfined, restartableScopePlusContext(Dispatchers.Unconfined, Dispatchers.Unconfined))
    }

    @Test
    fun testRestart() {
        fun CoroutineScope.job() = coroutineContext[Job]!!
        val initialJob = Job()
        val newJob = Job()
        var factoryInvoked = false
        val scope = RestartableCoroutineScope(initialJob) {
            factoryInvoked = true
            newJob
        }
        assertSame(initialJob, scope.job())
        assertTrue(scope.isActive)
        scope.job().cancel()
        assertFalse(scope.isActive)
        assertFalse(factoryInvoked)
        scope.restart()
        assertTrue(factoryInvoked)
        assertTrue(scope.isActive)
        assertNotSame(initialJob, scope.job())
        assertSame(newJob, scope.job())
    }

    @Test
    fun testIsRestartable() {
        val scope = CoroutineScope(Dispatchers.Unconfined)
        assertFalse(scope.isRestartable)
        val restartableScope = RestartableCoroutineScope(Dispatchers.Unconfined)
        assertTrue(restartableScope.isRestartable)
    }

    @Test
    fun testIsRestarted() {
        val scope = RestartableCoroutineScope(Dispatchers.Unconfined)
        assertFalse(scope.isRestarted)
        scope.coroutineContext[Job]!!.cancel()
        assertFalse(scope.isRestarted)
        scope.restart()
        assertTrue(scope.isRestarted)
    }

    @Test
    fun testRestartableMainScope() {
        assertSame(RestartableMainScope().coroutineContext[ContinuationInterceptor], Dispatchers.Main)
    }

    private fun scopePlusContext(c1: CoroutineContext, c2: CoroutineContext) =
        (ContextScope(c1) + c2).coroutineContext

    private fun restartableScopePlusContext(c1: CoroutineContext, c2: CoroutineContext) =
        (RestartableContextScope(c1) { Job() } + c2).coroutineContext
}
