/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.test.*

class SelectMemoryLeakStressTest : TestBase() {
    private val nRepeat = 1_000_000 * stressTestMultiplier

    @Test
    fun testLeakRegisterSend() = runTest {
        expect(1)
        val leak = Channel<String>()
        val data = Channel<Int>(1)
        repeat(nRepeat) { value ->
            data.send(value)
            val bigValue = bigValue() // new instance
            select {
                leak.onSend("LEAK") {
                    println("Capture big value into this lambda: $bigValue")
                    expectUnreached()
                }
                data.onReceive { received ->
                    assertEquals(value, received)
                    expect(value + 2)
                }
            }
        }
        finish(nRepeat + 2)
    }

    @Test
    fun testLeakRegisterReceive() = runTest {
        expect(1)
        val leak = Channel<String>()
        val data = Channel<Int>(1)
        repeat(nRepeat) { value ->
            val bigValue = bigValue() // new instance
            select {
                leak.onReceive {
                    println("Capture big value into this lambda: $bigValue")
                    expectUnreached()
                }
                data.onSend(value) {
                    expect(value + 2)
                }
            }
            assertEquals(value, data.receive())
        }
        finish(nRepeat + 2)
    }

    // capture big value for fast OOM in case of a bug
    private fun bigValue(): ByteArray = ByteArray(4096)
}