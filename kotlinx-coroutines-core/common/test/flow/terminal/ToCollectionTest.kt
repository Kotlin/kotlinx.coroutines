/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class ToCollectionTest : TestBase() {

    private val flow = flow {
        repeat(10) {
            emit(42)
        }
    }

    private val emptyFlow = flowOf<Int>()

    @Test
    fun testToList() = runTest {
        assertEquals(List(10) { 42 }, flow.toList())
        assertEquals(emptyList(), emptyFlow.toList())
    }

    @Test
    fun testToSet() = runTest {
        assertEquals(setOf(42), flow.toSet())
        assertEquals(emptySet(), emptyFlow.toSet())
    }
}
