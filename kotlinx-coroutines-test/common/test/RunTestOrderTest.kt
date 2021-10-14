/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.flow.*
import kotlin.test.*

class RunTestOrderTest {

    /** Tests that the [runTest] follows an execution order similar to `runBlocking`. */
    @Test
    fun testFlowsNotSkippingValues() = runTest {
        // https://github.com/Kotlin/kotlinx.coroutines/issues/1626#issuecomment-554632852
        val list = flowOf(1).onStart { emit(0) }
            .combine(flowOf("A")) { int, str -> "$str$int" }
            .toList()

        assertEquals(list, listOf("A0", "A1"))
    }

}