/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.*

/**
 * A simple stress-test that does select sending/receiving into opposite channels to ensure that they
 * don't deadlock. See https://github.com/Kotlin/kotlinx.coroutines/issues/504
 */
class SelectDeadlockStressTest : TestBase() {
    private val pool = newFixedThreadPoolContext(2, "SelectDeadlockStressTest")
    private val nSeconds = 30 * stressTestMultiplier

    @After
    fun tearDown() {
        pool.close()
    }

    @Test
    fun testStress() = runTest {
        val c1 = Channel<Long>(1)
        val c2 = Channel<Long>(1)
        val s = Array(4) { Stats() }
        launchSendReceive(c1, c2, s[0])
        launchSendReceive(c2, c1, s[1])
        launchSendReceive(c1, c2, s[2])
        launchSendReceive(c2, c1, s[3])
        for (i in 1..nSeconds) {
            delay(1000)
            val text = s.withIndex().joinToString("; ") { "#${it.index + 1} ${it.value}" }
            println("$i: $text")
        }
        coroutineContext.cancelChildren()
    }

    private class Stats {
        var sendIndex = 0L
        var receiveIndex = 0L

        override fun toString(): String = "send=$sendIndex, received=$receiveIndex"
    }

    private fun CoroutineScope.launchSendReceive(c1: Channel<Long>, c2: Channel<Long>, s: Stats) = launch(pool) {
        while (true) {
            if (s.sendIndex % 1000 == 0L) yield()
            select<Unit> {
                c1.onSend(s.sendIndex) {
                    s.sendIndex++
                }
                c2.onReceive { i ->
//                    assertEquals(s.receiveIndex, i)
                    s.receiveIndex++
                }
            }
        }
    }
}