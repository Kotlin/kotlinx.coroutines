/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class OnStartTest : TestBase() {
    @Test
    fun testEmitExample() = runTest {
        val flow = flowOf("a", "b", "c")
            .onStart { emit("Begin") }
        assertEquals(listOf("Begin", "a", "b", "c"), flow.toList())
    }

    @Test
    fun testTransparencyViolation() = runTest {
        val flow = emptyFlow<Int>().onStart {
            expect(2)
            coroutineScope {
                launch {
                    try {
                        emit(1)
                    } catch (e: IllegalStateException) {
                        expect(3)
                    }
                }
            }
        }
        expect(1)
        assertNull(flow.singleOrNull())
        finish(4)
    }
}
