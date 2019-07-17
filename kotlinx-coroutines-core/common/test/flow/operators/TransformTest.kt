/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class TransformTest : TestBase() {
    @Test
    fun testDoubleEmit() = runTest {
         val flow = flowOf(1, 2, 3)
             .transform {
                 emit(it)
                 emit(it)
             }
        assertEquals(listOf(1, 1, 2, 2, 3, 3), flow.toList())
    }
}