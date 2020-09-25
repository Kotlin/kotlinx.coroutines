/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class FirstJvmTest : TestBase() {

    @Test
    fun testTakeInterference() = runBlocking(Dispatchers.Default) {
        /*
         * This test tests a racy situation when outer channelFlow is being cancelled,
         * inner flow starts atomically in "CANCELLING" state, sends one element and completes
         * (=> cancels and drops element away), triggering NSEE in Flow.first operator
         */
        val values = (0..10000).asFlow().flatMapMerge(Int.MAX_VALUE) {
            channelFlow {
                val value = channelFlow { send(1) }.first()
                send(value)
            }
        }.take(1).toList()
        assertEquals(listOf(1), values)
    }
}