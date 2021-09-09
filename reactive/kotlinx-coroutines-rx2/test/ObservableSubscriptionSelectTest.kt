/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.rx2

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.selects.*
import org.junit.Test
import kotlin.onSuccess
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
        val channelA = source.toChannel()
        val channelB = source.toChannel()
        loop@ while (true) {
            val done: Int = select {
                channelA.onReceiveCatching { result ->
                    result.onSuccess { assertEquals(a++, it) }
                    if (result.isSuccess) 1 else 0
                }
                channelB.onReceiveCatching { result ->
                    result.onSuccess { assertEquals(b++, it) }
                    if (result.isSuccess) 2 else 0
                }
            }
            when (done) {
                0 -> break@loop
                1 -> {
                    val r = channelB.receiveCatching().getOrNull()
                    if (r != null) assertEquals(b++, r)
                }
                2 -> {
                    val r = channelA.receiveCatching().getOrNull()
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
