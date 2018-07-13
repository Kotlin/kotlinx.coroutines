/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlin.test.*


class BroadcastChannelFactoryTest {

    @Test
    fun testRendezvousChannelNotSupported() {
        assertFailsWith<IllegalArgumentException> { BroadcastChannel<Int>(0) }
    }

    @Test
    fun testLinkedListChannelNotSupported() {
        assertFailsWith<IllegalArgumentException> { BroadcastChannel<Int>(Channel.UNLIMITED) }
    }

    @Test
    fun testConflatedBroadcastChannel() {
        assertTrue { BroadcastChannel<Int>(Channel.CONFLATED) is ConflatedBroadcastChannel }
    }

    @Test
    fun testArrayBroadcastChannel() {
        assertTrue { BroadcastChannel<Int>(1) is ArrayBroadcastChannel }
        assertTrue { BroadcastChannel<Int>(10) is ArrayBroadcastChannel }
    }

    @Test
    fun testInvalidCapacityNotSupported() {
        assertFailsWith<IllegalArgumentException> { BroadcastChannel<Int>(-2) }
    }
}
