/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class FlowCancellationTest : TestBase() {

    @Test
    fun testEmitIsCooperative() = runTest {
        val latch = Channel<Unit>(1)
        val job = flow {
            expect(1)
            latch.send(Unit)
            while (true) {
                emit(42)
            }
        }.launchIn(this + Dispatchers.Default)

        latch.receive()
        expect(2)
        job.cancelAndJoin()
        finish(3)
    }

    @Test
    fun testIsActiveOnCurrentContext() = runTest {
        val latch = Channel<Unit>(1)
        val job = flow<Unit> {
            expect(1)
            latch.send(Unit)
            while (currentCoroutineContext().isActive) {
                // Do nothing
            }
        }.launchIn(this + Dispatchers.Default)

        latch.receive()
        expect(2)
        job.cancelAndJoin()
        finish(3)
    }
}