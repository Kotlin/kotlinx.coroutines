/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlin.test.*

/**
 * Tests for failures inside `onUndeliveredElement` handler in [Channel].
 */
class ChannelUndeliveredElementFailureTest : TestBase() {
    private val item = "LOST"
    private val onCancelFail: (String) -> Unit = { throw TestException(it) }
    private val shouldBeUnhandled: List<(Throwable) -> Boolean> = listOf({ it.isElementCancelException() })

    private fun Throwable.isElementCancelException() =
        this is UndeliveredElementException && cause is TestException && cause!!.message == item

    @Test
    fun testSendCancelledFail() = runTest(unhandled = shouldBeUnhandled) {
        val channel = Channel(onUndeliveredElement = onCancelFail)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            channel.send(item)
            expectUnreached()
        }
        job.cancel()
    }

    @Test
    fun testSendSelectCancelledFail() = runTest(unhandled = shouldBeUnhandled) {
        val channel = Channel(onUndeliveredElement = onCancelFail)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            select {
                channel.onSend(item) {
                    expectUnreached()
                }
            }
        }
        job.cancel()
    }

    @Test
    fun testReceiveCancelledFail() = runTest(unhandled = shouldBeUnhandled) {
        val channel = Channel(onUndeliveredElement = onCancelFail)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            channel.receive()
            expectUnreached() // will be cancelled before it dispatches
        }
        channel.send(item)
        job.cancel()
    }

    @Test
    fun testReceiveSelectCancelledFail() = runTest(unhandled = shouldBeUnhandled) {
        val channel = Channel(onUndeliveredElement = onCancelFail)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            select<Unit> {
                channel.onReceive {
                    expectUnreached()
                }
            }
            expectUnreached() // will be cancelled before it dispatches
        }
        channel.send(item)
        job.cancel()
    }

    @Test
    fun testReceiveCatchingCancelledFail() = runTest(unhandled = shouldBeUnhandled) {
        val channel = Channel(onUndeliveredElement = onCancelFail)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            channel.receiveCatching()
            expectUnreached() // will be cancelled before it dispatches
        }
        channel.send(item)
        job.cancel()
    }

    @Test
    fun testReceiveOrClosedSelectCancelledFail() = runTest(unhandled = shouldBeUnhandled) {
        val channel = Channel(onUndeliveredElement = onCancelFail)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            select<Unit> {
                channel.onReceiveCatching {
                    expectUnreached()
                }
            }
            expectUnreached() // will be cancelled before it dispatches
        }
        channel.send(item)
        job.cancel()
    }

    @Test
    fun testHasNextCancelledFail() = runTest(unhandled = shouldBeUnhandled) {
        val channel = Channel(onUndeliveredElement = onCancelFail)
        val job = launch(start = CoroutineStart.UNDISPATCHED) {
            channel.iterator().hasNext()
            expectUnreached() // will be cancelled before it dispatches
        }
        channel.send(item)
        job.cancel()
    }

    @Test
    fun testChannelCancelledFail() = runTest(expected = { it.isElementCancelException()}) {
        val channel = Channel(1, onUndeliveredElement = onCancelFail)
        channel.send(item)
        channel.cancel()
        expectUnreached()
    }

}
