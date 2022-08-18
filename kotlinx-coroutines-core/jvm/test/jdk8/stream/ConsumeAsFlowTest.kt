/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.stream

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import org.junit.Test
import java.lang.IllegalStateException
import kotlin.test.*

class ConsumeAsFlowTest : TestBase() {

    @Test
    fun testCollect() = runTest {
        val list = listOf(1, 2, 3)
        assertEquals(list, list.stream().consumeAsFlow().toList())
    }

    @Test
    fun testCollectInvokesClose() = runTest {
        val list = listOf(3, 4, 5)
        expect(1)
        assertEquals(list, list.stream().onClose { expect(2) }.consumeAsFlow().toList())
        finish(3)
    }

    @Test
    fun testCollectTwice() = runTest {
        val list = listOf(2, 3, 9)
        val flow = list.stream().onClose { expect(2) } .consumeAsFlow()
        expect(1)
        assertEquals(list, flow.toList())
        assertFailsWith<IllegalStateException> { flow.collect() }
        finish(3)
    }
}
