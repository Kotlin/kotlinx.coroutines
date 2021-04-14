/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.*
import kotlin.coroutines.*
import org.junit.rules.TestName
import org.junit.Rule

class StackTraceRecoveryResumeModeTest : TestBase() {

    @get:Rule
    val testName = TestName()

    @Test
    fun testUnconfined() = runTest {
        testResumeModeFastPath(Dispatchers.Unconfined)
    }

    @Test
    fun testNestedUnconfined() = runTest {
        withContext(Dispatchers.Unconfined) {
            testResumeModeFastPath(Dispatchers.Unconfined)
        }
    }

    @Test
    fun testNestedUnconfinedChangedContext() = runTest {
        withContext(Dispatchers.Unconfined) {
            testResumeModeFastPath(CoroutineName("Test"))
        }
    }

    @Test
    fun testEventLoopDispatcher() = runTest {
        testResumeModeFastPath(wrapperDispatcher())
    }

    @Test
    fun testNestedEventLoopDispatcher() = runTest {
        val dispatcher = wrapperDispatcher()
        withContext(dispatcher) {
            testResumeModeFastPath(dispatcher)
        }
    }

    @Test
    fun testNestedEventLoopChangedContext() = runTest {
        withContext(wrapperDispatcher()) {
            testResumeModeFastPath(CoroutineName("Test"))
        }
    }

    private suspend fun testResumeModeFastPath(context: CoroutineContext) {
        try {
            val channel = Channel<Int>()
            channel.close(RecoverableTestException())
            doFastPath(context, channel)
        } catch (e: Throwable) {
            verifyStackTrace("resume-mode/${testName.methodName}", e)
        }
    }

    private suspend fun doFastPath(context: CoroutineContext, channel: Channel<Int>) {
        yield()
        withContext(context, channel)
    }

    private suspend fun withContext(context: CoroutineContext, channel: Channel<Int>) {
        withContext(context) {
            channel.receive()
            yield()
        }
    }

    @Test
    fun testUnconfinedSuspending() = runTest {
        testResumeModeSuspending(Dispatchers.Unconfined)
    }

    @Test
    fun testNestedUnconfinedSuspending() = runTest {
        withContext(Dispatchers.Unconfined) {
            testResumeModeSuspending(Dispatchers.Unconfined)
        }
    }

    @Test
    fun testNestedUnconfinedChangedContextSuspending() = runTest {
        withContext(Dispatchers.Unconfined) {
            testResumeModeSuspending(CoroutineName("Test"))
        }
    }

    @Test
    fun testEventLoopDispatcherSuspending() = runTest {
        testResumeModeSuspending(wrapperDispatcher())
    }

    @Test
    fun testNestedEventLoopDispatcherSuspending() = runTest {
        val dispatcher = wrapperDispatcher()
        withContext(dispatcher) {
            testResumeModeSuspending(dispatcher)
        }
    }

    @Test
    fun testNestedEventLoopChangedContextSuspending() = runTest {
        withContext(wrapperDispatcher()) {
            testResumeModeSuspending(CoroutineName("Test"))
        }
    }

    private suspend fun testResumeModeSuspending(context: CoroutineContext) {
        try {
            val channel = Channel<Int>()
            val latch = Channel<Int>()
            GlobalScope.launch(coroutineContext) {
                latch.receive()
                expect(3)
                channel.close(RecoverableTestException())
            }
            doSuspendingPath(context, channel, latch)
        } catch (e: Throwable) {
            finish(4)
            verifyStackTrace("resume-mode/${testName.methodName}", e)
        }
    }

    private suspend fun doSuspendingPath(context: CoroutineContext, channel: Channel<Int>, latch: Channel<Int>) {
        yield()
        withContext(context, channel, latch)
    }

    private suspend fun withContext(context: CoroutineContext, channel: Channel<Int>, latch: Channel<Int>) {
        withContext(context) {
            expect(1)
            latch.send(1)
            expect(2)
            channel.receive()
            yield()
        }
    }
}