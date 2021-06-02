/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.operators

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.test.*

class ThrottleTest : TestBase() {
    @Test
    public fun testBasic() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            emit("A")
            delay(1500)
            emit("B")
            delay(500)
            emit("C")
            delay(250)
            emit("D")
            delay(2000)
            emit("E")
            expect(4)
        }

        expect(2)
        val result = flow.throttle(1000).toList()
        assertEquals(listOf("A", "B", "D", "E"), result)
        finish(5)
    }

    @Test
    public fun pendingValuesEmitAfterDelay() = withVirtualTime {
        val flow = flow {
            expect(2)
            emit("A")
            emit("B")
        }

        expect(1)
        val result = flow.throttle(1000).toList()
        assertEquals(listOf("A", "B"), result)
        finish(3)
    }

    @Test
    public fun testEmpty() = runTest {
        val result = emptyFlow<String>().throttle(1000).toList()
        assertEquals(emptyList(), result)
    }

    @Test
    public fun upstreamException() = runTest {
        val flow = flow {
            emit("A")
            throw TestException()
        }
        assertFailsWith<TestException>(flow)
    }

    @Test
    public fun testWithNulls() = runTest {
        val flow = flow {
            emit("A")
            emit(null)
        }
        val result = flow.throttle(1000).toList()
        assertEquals(listOf("A", null), result)
    }

    @Test
    public fun testRapidUpstream() = withVirtualTime {
        val flow = flow {
            repeat(100) {
                emit("A-$it")
            }
            delay(5000)
            repeat(100) {
                emit("B-$it")
            }
        }
        val result = flow.throttle(1000).toList()
        assertEquals(listOf("A-0", "A-99", "B-0", "B-99"), result)
        finish(1)
    }
}
