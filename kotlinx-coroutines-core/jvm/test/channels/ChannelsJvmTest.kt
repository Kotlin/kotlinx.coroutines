/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import org.junit.Test
import kotlin.test.*

class ChannelsJvmTest : TestBase() {

    @Test
    fun testBlocking() {
        val ch = Channel<Int>()
        val sum = GlobalScope.async {
            var sum = 0
            ch.consumeEach { sum += it }
            sum
        }
        repeat(10) {
            ch.sendBlocking(it)
        }
        ch.close()
        assertEquals(45, runBlocking { sum.await() })
    }
}
