/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.test.*

class OnStartTest : TestBase() {
    @Test
    fun testEmitExample() = runTest {
        val flow = flowOf("a", "b", "c")
            .onStart { emit("Begin") }
        assertEquals(listOf("Begin", "a", "b", "c"), flow.toList())
    }
}