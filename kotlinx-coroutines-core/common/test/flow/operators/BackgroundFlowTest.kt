/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

/**
 * Test some flow operators in background thread,
 * mostly for the purpose of checking Kotlin/Native implementation.
 */
class BackgroundFlowTest : TestBase() {
    @Test
    fun testFlowCombine() = runTest {
        withContext(Dispatchers.Default) {
            val flow = flowOf(1)
            val combo = combine(flow, flow) { a, b -> a + b }
            assertEquals(2, combo.first())
        }
    }
}