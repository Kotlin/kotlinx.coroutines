/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx3

import kotlinx.coroutines.*
import kotlinx.coroutines.selects.*
import org.junit.Test
import kotlin.test.*

class ObservableSubscriptionSelectTest : TestBase() {
    @Test
    fun testSelect() = runTest {
        // source with n ints
        val n = 1000 * stressTestMultiplier
        val source = rxObservable { repeat(n) { send(it) } }
        var a = 0
        var b = 0
        // open two subs
        val channelA = source.openSubscription()
        val channelB = source.openSubscription()
        loop@ while (true) {
            val done: Int = select {
                channelA.onReceiveOrNull {
                    if (it != null) assertEquals(a++, it)
                    if (it == null) 0 else 1
                }
                channelB.onReceiveOrNull {
                    if (it != null) assertEquals(b++, it)
                    if (it == null) 0 else 2
                }
            }
            when (done) {
                0 -> break@loop
                1 -> {
                    val r = channelB.receiveOrNull()
                    if (r != null) assertEquals(b++, r)
                }
                2 -> {
                    val r = channelA.receiveOrNull()
                    if (r != null) assertEquals(a++, r)
                }
            }
        }
        channelA.cancel()
        channelB.cancel()
        // should receive one of them fully
        assertTrue(a == n || b == n)
    }
}
