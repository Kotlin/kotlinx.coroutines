/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.rx1

import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.selects.*
import org.junit.*
import org.junit.Assert.*
import org.junit.runner.*
import org.junit.runners.*
import kotlin.coroutines.experimental.*

@RunWith(Parameterized::class)
class ObservableSubscriptionSelectTest(val request: Int) : TestBase() {
    companion object {
        @Parameterized.Parameters(name = "request = {0}")
        @JvmStatic
        fun params(): Collection<Array<Any>> = listOf(0, 1, 10).map { arrayOf<Any>(it) }
    }

    @Test
    fun testSelect() = runTest {
        // source with n ints
        val n = 1000 * stressTestMultiplier
        val source = rxObservable(coroutineContext) { repeat(n) { send(it) } }
        var a = 0
        var b = 0
        // open two subs
        val channelA = source.openSubscription(request)
        val channelB = source.openSubscription(request)
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