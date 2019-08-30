/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.selects

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import org.junit.*
import org.junit.Test
import kotlin.test.*

/**
 * A simple stress-test that does select sending/receiving into opposite channels to ensure that they
 * don't deadlock. See https://github.com/Kotlin/kotlinx.coroutines/issues/504
 */
class SelectDeadlockStressTest : TestBase() {
    private val pool = newFixedThreadPoolContext(2, "SelectDeadlockStressTest")
    private val nSeconds = 3 * stressTestMultiplier

    @After
    fun tearDown() {
        pool.close()
    }

    @Test
    fun testStress() = runTest {
        val c1 = Channel<Long>()
        val c2 = Channel<Long>()
        val s1 = Stats()
        val s2 = Stats()
        launchSendReceive(c1, c2, s1)
        launchSendReceive(c2, c1, s2)
        for (i in 1..nSeconds) {
            delay(1000)
            println("$i: First: $s1; Second: $s2")
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
                    assertEquals(s.receiveIndex, i)
                    s.receiveIndex++
                }
            }
        }
    }
}