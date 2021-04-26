/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class ChannelsJvmTest : TestBase() {

    @Test
    fun testTrySendBlocking() {
        val ch = Channel<Int>()
        val sum = GlobalScope.async {
            var sum = 0
            ch.consumeEach { sum += it }
            sum
        }
        repeat(10) {
            assertTrue(ch.trySendBlocking(it).isSuccess)
        }
        ch.close()
        assertEquals(45, runBlocking { sum.await() })
    }

    // Uncomment lines when migrated to 1.5, these are bugs in inline classes codegen
    @Test
    fun testTrySendBlockingClosedChannel() {
        run {
            val channel = Channel<Unit>().also { it.close() }
            channel.trySendBlocking(Unit)
                .onSuccess { expectUnreached() }
                .onFailure { assertTrue(it is ClosedSendChannelException) }
//                .also { assertTrue { it.isClosed } }
        }

        run {
            val channel = Channel<Unit>().also { it.close(TestException()) }
            channel.trySendBlocking(Unit)
                .onSuccess { expectUnreached() }
                .onFailure { assertTrue(it is TestException) }
//                .also { assertTrue { it.isClosed } }
        }

        run {
            val channel = Channel<Unit>().also { it.cancel(TestCancellationException()) }
            channel.trySendBlocking(Unit)
                .onSuccess { expectUnreached() }
                .onFailure { assertTrue(it is TestCancellationException) }
//                .also { assertTrue { it.isClosed } }
        }
    }

}
