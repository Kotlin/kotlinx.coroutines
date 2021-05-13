/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class RepeatTest : TestBase() {

    @Test
    fun testRepeat() = runTest {
        val flow = flow { emit(1) }
        assertEquals(3, flow.repeat(3).sum())
    }

    @Test
    fun testRepeatUntil() = runTest {
        val flow = flow { emit(1) }
        var count = 0
        assertEquals(3, flow.repeatUntil { count++ == 3 }.sum())
    }
}
