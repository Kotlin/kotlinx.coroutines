/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class ShareInFusionTest : TestBase() {
    /**
     * Test perfect fusion for operators **after** [shareIn].
     */
    @Test
    fun testOperatorFusion() = runTest {
        val sh = emptyFlow<Int>().shareIn(this, SharingStarted.Eagerly)
        assertTrue(sh !is MutableSharedFlow<*>) // cannot be cast to mutable shared flow!!!
        assertSame(sh, (sh as Flow<*>).cancellable())
        assertSame(sh, (sh as Flow<*>).flowOn(Dispatchers.Default))
        assertSame(sh, sh.buffer(Channel.RENDEZVOUS))
        coroutineContext.cancelChildren()
    }

    @Test
    fun testFlowOnContextFusion() = runTest {
        val flow = flow {
            assertEquals("FlowCtx", currentCoroutineContext()[CoroutineName]?.name)
            emit("OK")
        }.flowOn(CoroutineName("FlowCtx"))
        assertEquals("OK", flow.shareIn(this, SharingStarted.Eagerly, 1).first())
        coroutineContext.cancelChildren()
    }

    /**
     * Tests that `channelFlow { ... }.buffer(x)` works according to the [channelFlow] docs, and subsequent
     * application of [shareIn] does not leak upstream.
     */
    @Test
    fun testChannelFlowBufferShareIn() = runTest {
        expect(1)
        val flow = channelFlow {
            // send a batch of 10 elements using [offer]
            for (i in 1..10) {
                assertTrue(trySend(i).isSuccess) // offer must succeed, because buffer
            }
            send(0) // done
        }.buffer(10) // request a buffer of 10
        // ^^^^^^^^^ buffer stays here
        val shared = flow.shareIn(this, SharingStarted.Eagerly)
        shared
            .takeWhile { it > 0 }
            .collect { i -> expect(i + 1) }
        finish(12)
    }
}
