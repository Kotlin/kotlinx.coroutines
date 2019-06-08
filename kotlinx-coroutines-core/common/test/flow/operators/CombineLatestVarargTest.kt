/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class CombineLatestVarargTest : TestBase() {

    @Test
    fun testThreeParameters() = runTest {
        val flow = flowOf("1").combineLatest(flowOf(2), flowOf(null)) { a, b, c ->
            a + b + c
        }

        assertEquals("12null", flow.single())
    }

    @Test
    fun testFourParameters() = runTest {
        val flow = flowOf("1").combineLatest(flowOf(2), flowOf("3"), flowOf(null)) { a, b, c, d ->
            a + b + c + d
        }

        assertEquals("123null", flow.single())
    }

    @Test
    fun testFiveParameters() = runTest {
        val flow =
            flowOf("1").combineLatest(flowOf(2), flowOf("3"), flowOf(4.toByte()), flowOf(null)) { a, b, c, d, e ->
                a + b + c + d + e
            }

        assertEquals("1234null", flow.single())
    }

    @Test
    fun testVararg() = runTest {
        val flow = flowOf("1").combineLatest(
            flowOf(2),
            flowOf("3"),
            flowOf(4.toByte()),
            flowOf("5"),
            flowOf(null)
        ) { arr -> arr.joinToString("") }
        assertEquals("12345null", flow.single())
    }

    @Test
    fun testEmptyVararg() = runTest {
        val list = flowOf(1, 2, 3).combineLatest { args: Array<Any?> -> args[0] }.toList()
        assertEquals(listOf(1, 2, 3), list)
    }

    @Test
    fun testNonNullableAny() = runTest {
        val value = flowOf(1).combineLatest(flowOf(2)) { args: Array<Int> ->
            @Suppress("USELESS_IS_CHECK")
            assertTrue(args is Array<Int>)
            args[0] + args[1]
        }.single()
        assertEquals(3, value)
    }
}
