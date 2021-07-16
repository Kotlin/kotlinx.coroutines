/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.time.*
import java.time.*
import kotlin.test.*

class FlowThrottleLatestTest : TestBase() {

    @Test
    fun testBasic() = withVirtualTime {
        expect(1)
        val flow = flow {
            expect(3)
            emit("A")
            delay(Duration.ofMillis(1500))
            emit("B")
            delay(Duration.ofMillis(500))
            emit("C")
            delay(Duration.ofMillis(250))
            emit("D")
            delay(Duration.ofMillis(2000))
            emit("E")
            expect(4)
        }

        expect(2)
        val result = flow.throttleLatest(Duration.ofMillis(1000)).toList()
        assertEquals(listOf("A", "B", "D", "E"), result)
        finish(5)
    }
}