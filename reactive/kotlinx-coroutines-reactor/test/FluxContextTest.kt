/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.reactor

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.reactive.*
import org.junit.*
import org.junit.Test
import reactor.core.publisher.*
import kotlin.test.*

class FluxContextTest : TestBase() {
    private val dispatcher = newSingleThreadContext("FluxContextTest")

    @After
    fun tearDown() {
        dispatcher.close()
    }

    @Test
    fun testFluxCreateAsFlowThread() = runTest {
        expect(1)
        val mainThread = Thread.currentThread()
        val dispatcherThread = withContext(dispatcher) { Thread.currentThread() }
        assertTrue(dispatcherThread != mainThread)
        Flux.create<String> {
            assertEquals(dispatcherThread, Thread.currentThread())
            it.next("OK")
            it.complete()
        }
            .asFlow()
            .flowOn(dispatcher)
            .collect {
                expect(2)
                assertEquals("OK", it)
                assertEquals(mainThread, Thread.currentThread())
            }
        finish(3)
    }
}