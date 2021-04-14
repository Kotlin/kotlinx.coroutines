/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.Test
import reactor.core.publisher.*
import kotlin.test.*

class BackpressureTest : TestBase() {
    @Test
    fun testBackpressureDropDirect() = runTest {
        expect(1)
        Flux.fromArray(arrayOf(1))
            .onBackpressureDrop()
            .collect {
                assertEquals(1, it)
                expect(2)
            }
        finish(3)
    }

    @Test
    fun testBackpressureDropFlow() = runTest {
        expect(1)
        Flux.fromArray(arrayOf(1))
            .onBackpressureDrop()
            .asFlow()
            .collect {
                assertEquals(1, it)
                expect(2)
            }
        finish(3)
    }

    @Test
    fun testCooperativeCancellation() = runTest {
        val flow = Flux.fromIterable((0L..Long.MAX_VALUE)).asFlow()
        flow.onEach { if (it > 10) currentCoroutineContext().cancel() }.launchIn(this + Dispatchers.Default).join()
    }

    @Test
    fun testCooperativeCancellationForBuffered() = runTest(expected = { it is CancellationException }) {
        val flow = Flux.fromIterable((0L..Long.MAX_VALUE)).asFlow()
        val channel = flow.onEach { if (it > 10) currentCoroutineContext().cancel() }.produceIn(this + Dispatchers.Default)
        channel.consumeEach { /* Do nothing, just consume elements */ }
    }
}