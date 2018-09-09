/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class ProduceConsumeTest : TestBase() {

    @Test
    fun testRendezvous() = runTest {
        testProducer(1)
    }

    @Test
    fun testSmallBuffer() = runTest {
        testProducer(1)
    }

    @Test
    fun testMediumBuffer() = runTest {
        testProducer(10)
    }

    @Test
    fun testLargeMediumBuffer() = runTest {
        testProducer(1000)
    }

    @Test
    fun testUnlimited() = runTest {
        testProducer(Channel.UNLIMITED)
    }

    private suspend fun testProducer(producerCapacity: Int) {
        testProducer(1, producerCapacity)
        testProducer(10, producerCapacity)
        testProducer(100, producerCapacity)
    }

    private suspend fun testProducer(messages: Int, producerCapacity: Int) {
        var sentAll = false
        val producer = GlobalScope.produce(coroutineContext, capacity = producerCapacity) {
            for (i in 1..messages) {
                send(i)
            }
            sentAll = true
        }
        var consumed = 0
        for (x in producer) {
            consumed++
        }
        assertTrue(sentAll)
        assertEquals(messages, consumed)
    }
}
