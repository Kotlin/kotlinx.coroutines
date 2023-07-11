/*
 * Copyright 2016-2022 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package channels

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.Test

class ChannelMemoryLeakStressTest : TestBase()  {
    private val nRepeat = 1_000_000 * stressTestMultiplier

    @Test
    fun test() = runTest {
        val c = Channel<Any>(1)
        repeat(nRepeat) {
            c.send(bigValue())
            c.receive()
        }
    }

    // capture big value for fast OOM in case of a bug
    private fun bigValue(): ByteArray = ByteArray(4096)
}
