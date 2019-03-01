/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("DeferredResultUnused", "DEPRECATION")

package kotlinx.coroutines.exceptions

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.*
import kotlin.coroutines.*

class StackTraceRecoveryNestedChannelsTest : TestBase() {

    private val channel = Channel<Int>(0)

    private suspend fun sendWithContext(ctx: CoroutineContext) = withContext(ctx) {
        sendInChannel()
        yield() // TCE
    }

    private suspend fun sendInChannel() {
        channel.send(42)
        yield() // TCE
    }

    private suspend fun sendFromScope() = coroutineScope {
        sendWithContext(wrapperDispatcher(coroutineContext))
    }

    @Test
    fun testOfferWithCurrentContext() = runTest {
        channel.close(RecoverableTestException())

        try {
            yield() // Will be fixed in 1.3.20 after KT-27190
            sendWithContext(coroutineContext)
        } catch (e: Exception) {
            verifyStackTrace(e,
                "kotlinx.coroutines.RecoverableTestException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$testOfferWithCurrentContext\$1.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:34)\n" +
                    "\t(Coroutine boundary)\n" +
                    "\tat kotlinx.coroutines.channels.AbstractSendChannel.offer(AbstractChannel.kt:180)\n" +
                    "\tat kotlinx.coroutines.channels.AbstractSendChannel.send(AbstractChannel.kt:168)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest.sendInChannel(StackTraceRecoveryNestedChannelsTest.kt:24)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$sendWithContext\$2.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:19)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$sendWithContext\$2.invoke(StackTraceRecoveryNestedChannelsTest.kt)\n" +
                    "\tat kotlinx.coroutines.intrinsics.UndispatchedKt.startUndispatchedOrReturn(Undispatched.kt:85)\n" +
                    "\tat kotlinx.coroutines.BuildersKt__Builders_commonKt.withContext(Builders.common.kt:146)\n" +
                    "\tat kotlinx.coroutines.BuildersKt.withContext(Unknown Source)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest.sendWithContext(StackTraceRecoveryNestedChannelsTest.kt:18)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$testOfferWithCurrentContext\$1.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:37)\n" +
                "Caused by: kotlinx.coroutines.RecoverableTestException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$testOfferWithCurrentContext\$1.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:34)\n" +
                    "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)\n")
        }
    }

    @Test
    fun testOfferWithContextWrapped() = runTest {
        channel.close(RecoverableTestException())

        try {
            sendWithContext(wrapperDispatcher(coroutineContext))
        } catch (e: Exception) {
            verifyStackTrace(e,
                "kotlinx.coroutines.RecoverableTestException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$testOfferWithContextWrapped\$1.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:59)\n" +
                    "\t(Coroutine boundary)\n" +
                    "\tat kotlinx.coroutines.channels.AbstractSendChannel.offer(AbstractChannel.kt:180)\n" +
                    "\tat kotlinx.coroutines.channels.AbstractSendChannel.send(AbstractChannel.kt:168)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest.sendInChannel(StackTraceRecoveryNestedChannelsTest.kt:24)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$sendWithContext\$2.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:19)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$testOfferWithContextWrapped\$1.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:62)\n" +
            "Caused by: kotlinx.coroutines.RecoverableTestException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$testOfferWithContextWrapped\$1.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:59)\n" +
                    "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)")
        }
    }

    @Test
    fun testOfferFromScope() = runTest {
        channel.close(RecoverableTestException())

        try {
            sendFromScope()
        } catch (e: Exception) {
            verifyStackTrace(e,
                "kotlinx.coroutines.RecoverableTestException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$testOfferFromScope\$1.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:81)\n" +
                    "\t(Coroutine boundary)\n" +
                    "\tat kotlinx.coroutines.channels.AbstractSendChannel.offer(AbstractChannel.kt:180)\n" +
                    "\tat kotlinx.coroutines.channels.AbstractSendChannel.send(AbstractChannel.kt:168)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest.sendInChannel(StackTraceRecoveryNestedChannelsTest.kt:24)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$sendWithContext\$2.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:19)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$sendFromScope\$2.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:28)\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$testOfferFromScope\$1.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:84)\n" +
                 "Caused by: kotlinx.coroutines.RecoverableTestException\n" +
                    "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$testOfferFromScope\$1.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:81)\n" +
                    "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)")
        }
    }

    // Slow path via suspending send
    @Test
    fun testSendFromScope() = runTest {
        val deferred = async {
            try {
                expect(1)
                sendFromScope()
            } catch (e: Exception) {
                verifyStackTrace(e,
                    "kotlinx.coroutines.RecoverableTestCancellationException\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$testSendFromScope\$1.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:118)\n" +
                        "\t(Coroutine boundary)\n" +
                        "\tat kotlinx.coroutines.channels.AbstractSendChannel.offer(AbstractChannel.kt:180)\n" +
                        "\tat kotlinx.coroutines.channels.AbstractSendChannel.send(AbstractChannel.kt:168)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest.sendInChannel(StackTraceRecoveryNestedChannelsTest.kt:24)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$sendWithContext\$2.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:19)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$sendFromScope\$2.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:29)\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$testSendFromScope\$1\$deferred\$1.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:109)\n" +
                    "Caused by: kotlinx.coroutines.RecoverableTestCancellationException\n" +
                        "\tat kotlinx.coroutines.exceptions.StackTraceRecoveryNestedChannelsTest\$testSendFromScope\$1.invokeSuspend(StackTraceRecoveryNestedChannelsTest.kt:118)\n" +
                        "\tat kotlin.coroutines.jvm.internal.BaseContinuationImpl.resumeWith(ContinuationImpl.kt:32)")
            }
        }

        yield()
        expect(2)
        // Cancel is an analogue of `produce` failure, just a shorthand
        channel.cancel(RecoverableTestCancellationException())
        finish(3)
        deferred.await()
    }
}
