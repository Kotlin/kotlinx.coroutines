/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels8

import kotlinx.coroutines.TestBase
import kotlinx.coroutines.channels.asReceiveChannel
import kotlinx.coroutines.channels.toList
import kotlinx.coroutines.runBlocking
import org.junit.Assert.assertEquals
import org.junit.Test
import java.util.stream.Collectors

class ChannelsTest : TestBase() {
    private val testList = listOf(1, 2, 3)

    @Test
    fun testCollect() = runBlocking {
        assertEquals(testList, testList.asReceiveChannel().collect(Collectors.toList()))
    }

    @Test
    fun testStreamAsReceiveChannel() = runBlocking {
        assertEquals(testList, testList.stream().asReceiveChannel().toList())
    }

    @Test
    fun testReceiveChannelAsStream() {
        assertEquals(testList, testList.asReceiveChannel().asStream().collect(Collectors.toList()))
    }
}
