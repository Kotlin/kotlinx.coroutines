/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class FlowViaChannelTest : TestBase() {
    @Test
    fun testRegular() = runTest {
        val flow = flowViaChannel<Int> {
            it.send(1)
            it.send(2)
            it.close()
        }
        assertEquals(listOf(1, 2), flow.toList())
    }

    @Test
    fun testConflated() = runTest {
        val flow = flowViaChannel<Int>(bufferSize = Channel.CONFLATED) {
            it.send(1)
            it.send(2)
            it.close()
        }
        assertEquals(listOf(1), flow.toList())
    }
}
