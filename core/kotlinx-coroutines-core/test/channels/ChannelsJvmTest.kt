/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import org.junit.Test
import kotlin.test.*

class ChannelsJvmTest : TestBase() {

    @Test
    fun testBlocking() {
        val ch = Channel<Int>()
        val sum = GlobalScope.async {
            ch.sumBy { it }
        }
        repeat(10) {
            ch.sendBlocking(it)
        }
        ch.close()
        assertEquals(45, runBlocking { sum.await() })
    }
}
