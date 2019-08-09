/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class CombineParametersTest : TestBase() {

    @Test
    fun testThreeParameters() = runTest {
        val flow = combine(flowOf("1"), flowOf(2), flowOf(null)) { a, b, c -> a + b + c }
        assertEquals("12null", flow.single())

        val flow2 = combineTransform(flowOf("1"), flowOf(2), flowOf(null)) { a, b, c -> emit(a + b + c) }
        assertEquals("12null", flow2.single())
    }

    @Test
    fun testThreeParametersTransform() = runTest {
        val flow = combineTransform(flowOf("1"), flowOf(2), flowOf(null)) { a, b, c -> emit(a + b + c) }
        assertEquals("12null", flow.single())
    }

    @Test
    fun testFourParameters() = runTest {
        val flow = combine(flowOf("1"), flowOf(2), flowOf("3"), flowOf(null)) { a, b, c, d -> a + b + c + d }
        assertEquals("123null", flow.single())
    }

    @Test
    fun testFourParametersTransform() = runTest {
        val flow = combineTransform(flowOf("1"), flowOf(2), flowOf("3"), flowOf(null)) { a, b, c, d ->
            emit(a + b + c + d)
        }
        assertEquals("123null", flow.single())
    }

    @Test
    fun testFiveParameters() = runTest {
        val flow = combine(flowOf("1"), flowOf(2), flowOf("3"), flowOf(4.toByte()), flowOf(null)) { a, b, c, d, e ->
                a + b + c + d + e
            }
        assertEquals("1234null", flow.single())
    }

    @Test
    fun testFiveParametersTransform() = runTest {
        val flow =
            combineTransform(flowOf("1"), flowOf(2), flowOf("3"), flowOf(4.toByte()), flowOf(null)) { a, b, c, d, e ->
                emit(a + b + c + d + e)
            }
        assertEquals("1234null", flow.single())
    }

    @Test
    fun testNonMatchingTypes() = runTest {
        val flow = combine(flowOf(1), flowOf("2")) { args: Array<Any?> ->
            args[0]?.toString() + args[1]?.toString()
        }
        assertEquals("12", flow.single())
    }

    @Test
    fun testNonMatchingTypesIterable() = runTest {
        val flow = combine(listOf(flowOf(1), flowOf("2"))) { args: Array<Any?> ->
            args[0]?.toString() + args[1]?.toString()
        }
        assertEquals("12", flow.single())
    }

    @Test
    fun testVararg() = runTest {
        val flow = combine(
            flowOf("1"),
            flowOf(2),
            flowOf("3"),
            flowOf(4.toByte()),
            flowOf("5"),
            flowOf(null)
        ) { arr -> arr.joinToString("") }
        assertEquals("12345null", flow.single())
    }

    @Test
    fun testVarargTransform() = runTest {
        val flow = combineTransform(
            flowOf("1"),
            flowOf(2),
            flowOf("3"),
            flowOf(4.toByte()),
            flowOf("5"),
            flowOf(null)
        ) { arr -> emit(arr.joinToString("")) }
        assertEquals("12345null", flow.single())
    }

    @Test
    fun testEmptyVararg() = runTest {
        val list = combine(flowOf(1, 2, 3)) { args: Array<Any?> -> args[0] }.toList()
        assertEquals(listOf(1, 2, 3), list)
    }

    @Test
    fun testEmptyVarargTransform() = runTest {
        val list = combineTransform(flowOf(1, 2, 3)) { args: Array<Any?> -> emit(args[0]) }.toList()
        assertEquals(listOf(1, 2, 3), list)
    }

    @Test
    fun testReified() = runTest {
        val value = combine(flowOf(1), flowOf(2)) { args: Array<Int> ->
            @Suppress("USELESS_IS_CHECK")
            assertTrue(args is Array<Int>)
            args[0] + args[1]
        }.single()
        assertEquals(3, value)
    }

    @Test
    fun testReifiedTransform() = runTest {
        val value = combineTransform(flowOf(1), flowOf(2)) { args: Array<Int> ->
            @Suppress("USELESS_IS_CHECK")
            assertTrue(args is Array<Int>)
            emit(args[0] + args[1])
        }.single()
        assertEquals(3, value)
    }

    @Test
    fun testEmpty() = runTest {
        val value = combineTransform { args: Array<Int> ->
            emit(args[0] + args[1])
        }.singleOrNull()
        assertNull(value)
    }

    @Test
    fun testEmptyIterable() = runTest {
        val value = combineTransform(emptyList()) { args: Array<Int> ->
            emit(args[0] + args[1])
        }.singleOrNull()
        assertNull(value)
    }

    @Test
    fun testEmptyReified() = runTest {
        val value = combineTransform { args: Array<Int> ->
            emit(args[0] + args[1])
        }.singleOrNull()
        assertNull(value)
    }

    @Test
    fun testEmptyIterableReified() = runTest {
        val value = combineTransform(emptyList()) { args: Array<Int> ->
            emit(args[0] + args[1])
        }.singleOrNull()
        assertNull(value)
    }
}
