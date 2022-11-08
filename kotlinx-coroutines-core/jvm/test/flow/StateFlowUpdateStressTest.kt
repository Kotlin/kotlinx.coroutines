/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import org.junit.*
import kotlin.test.*
import kotlin.test.Test

class StateFlowUpdateStressTest : TestBase() {
    private val iterations = 1_000_000 * stressTestMultiplier

    @get:Rule
    public val executor = ExecutorRule(2)

    @Test
    fun testUpdate() = doTest { update { it + 1 } }

    @Test
    fun testUpdateAndGet() = doTest { updateAndGet { it + 1 } }

    @Test
    fun testGetAndUpdate() = doTest { getAndUpdate { it + 1 } }

    private fun doTest(increment: MutableStateFlow<Int>.() -> Unit) = runTest {
        val flow = MutableStateFlow(0)
        val j1 = launch(Dispatchers.Default) {
            repeat(iterations / 2) {
                flow.increment()
            }
        }

        val j2 = launch(Dispatchers.Default) {
            repeat(iterations / 2) {
                flow.increment()
            }
        }

        joinAll(j1, j2)
        assertEquals(iterations, flow.value)
    }
}
