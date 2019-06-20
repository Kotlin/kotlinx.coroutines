/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class DistinctUntilChangedTest : TestBase() {

    private class Box(val i: Int)

    @Test
    fun testDistinctUntilChanged() = runTest {
        val flow = flowOf(1, 1, 2, 2, 1).distinctUntilChanged()
        assertEquals(4, flow.sum())
    }

    @Test
    fun testDistinctUntilChangedKeySelector() = runTest {
        val flow = flow {
            emit(Box(1))
            emit(Box(1))
            emit(Box(2))
            emit(Box(1))
        }

        val sum1 = flow.distinctUntilChanged().map { it.i }.sum()
        val sum2 = flow.distinctUntilChangedBy(Box::i).map { it.i }.sum()
        assertEquals(5, sum1)
        assertEquals(4, sum2)
    }

    @Test
    fun testDistinctUntilChangedAreEquivalent() = runTest {
        val flow = flow {
            emit(Box(1))
            emit(Box(1))
            emit(Box(2))
            emit(Box(1))
        }

        val sum1 = flow.distinctUntilChanged().map { it.i }.sum()
        val sum2 = flow.distinctUntilChanged { old, new -> old.i == new.i }.map { it.i }.sum()
        assertEquals(5, sum1)
        assertEquals(4, sum2)
    }

    @Test
    fun testDistinctUntilChangedAreEquivalentSingleValue() = runTest {
        val flow = flowOf(1)
        val values = flow.distinctUntilChanged { _, _ -> fail("Expected not to compare single value.") }.toList()
        assertEquals(listOf(1), values)
    }

    @Test
    fun testThrowingKeySelector() = runTest {
        val flow = flow {
            coroutineScope {
                launch(start = CoroutineStart.ATOMIC) {
                    hang { expect(3) }
                }
                expect(2)
                emit(1)
            }
        }.distinctUntilChangedBy { throw TestException() }

        expect(1)
        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testThrowingAreEquivalent() = runTest {
        val flow = flow {
            coroutineScope {
                launch(start = CoroutineStart.ATOMIC) {
                    hang { expect(3) }
                }
                expect(2)
                emit(1)
                emit(2)
            }
        }.distinctUntilChanged { _, _ -> throw TestException() }

        expect(1)
        assertFailsWith<TestException>(flow)
        finish(4)
    }

    @Test
    fun testDistinctUntilChangedNull() = runTest {
        val flow = flowOf(null, 1, null, null).distinctUntilChanged()
        assertEquals(listOf(null, 1, null), flow.toList())
    }
}
