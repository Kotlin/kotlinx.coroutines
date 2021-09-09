/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class SafeFlowTest : TestBase() {

    @Test
    fun testEmissionsFromDifferentStateMachine() = runTest {
        val result = flow<Int> {
            emit1(1)
            emit2(2)
        }.onEach { yield() }.toList()
        assertEquals(listOf(1, 2), result)
        finish(3)
    }

    private suspend fun FlowCollector<Int>.emit1(expect: Int) {
        emit(expect)
        expect(expect)
    }

    private suspend fun FlowCollector<Int>.emit2(expect: Int) {
        emit(expect)
        expect(expect)
    }
}
