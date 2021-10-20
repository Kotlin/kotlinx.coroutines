/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlin.test.*

class TestCoroutineDispatcherOrderTest {

    private val actionIndex = atomic(0)
    private val finished = atomic(false)

    private fun expect(index: Int) {
        val wasIndex = actionIndex.incrementAndGet()
        check(index == wasIndex) { "Expecting action index $index but it is actually $wasIndex" }
    }

    private fun finish(index: Int) {
        expect(index)
        check(!finished.getAndSet(true)) { "Should call 'finish(...)' at most once" }
    }

    @Test
    fun testAdvanceTimeBy_progressesOnEachDelay() {
        val dispatcher = TestCoroutineDispatcher()
        val scope = TestCoroutineScope(dispatcher)

        expect(1)
        scope.launch {
            expect(2)
            delay(1_000)
            assertEquals(1_000, dispatcher.currentTime)
            expect(4)
            delay(5_00)
            assertEquals(1_500, dispatcher.currentTime)
            expect(5)
            delay(501)
            assertEquals(2_001, dispatcher.currentTime)
            expect(7)
        }
        expect(3)
        assertEquals(0, dispatcher.currentTime)
        dispatcher.advanceTimeBy(2_000)
        expect(6)
        assertEquals(2_000, dispatcher.currentTime)
        dispatcher.advanceTimeBy(2)
        expect(8)
        assertEquals(2_002, dispatcher.currentTime)
        scope.cleanupTestCoroutines()
        finish(9)
    }
}