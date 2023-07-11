/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.test.*


class ChannelFactoryTest : TestBase() {
    @Test
    fun testRendezvousChannel() {
        assertTrue(Channel<Int>() is BufferedChannel)
        assertTrue(Channel<Int>(0) is BufferedChannel)
    }

    @Test
    fun testUnlimitedChannel() {
        assertTrue(Channel<Int>(Channel.UNLIMITED) is BufferedChannel)
        assertTrue(Channel<Int>(Channel.UNLIMITED, BufferOverflow.DROP_OLDEST) is BufferedChannel)
        assertTrue(Channel<Int>(Channel.UNLIMITED, BufferOverflow.DROP_LATEST) is BufferedChannel)
    }

    @Test
    fun testConflatedChannel() {
        assertTrue(Channel<Int>(Channel.CONFLATED) is ConflatedBufferedChannel)
        assertTrue(Channel<Int>(1, BufferOverflow.DROP_OLDEST) is ConflatedBufferedChannel)
    }

    @Test
    fun testBufferedChannel() {
        assertTrue(Channel<Int>(1) is BufferedChannel)
        assertTrue(Channel<Int>(1, BufferOverflow.DROP_LATEST) is ConflatedBufferedChannel)
        assertTrue(Channel<Int>(10) is BufferedChannel)
    }

    @Test
    fun testInvalidCapacityNotSupported() {
        assertFailsWith<IllegalArgumentException> { Channel<Int>(-3) }
    }
    
    @Test
    fun testUnsupportedBufferOverflow() {
        assertFailsWith<IllegalArgumentException> { Channel<Int>(Channel.CONFLATED, BufferOverflow.DROP_OLDEST) }
        assertFailsWith<IllegalArgumentException> { Channel<Int>(Channel.CONFLATED, BufferOverflow.DROP_LATEST) }
    }
}
