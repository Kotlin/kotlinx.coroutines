/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.time

import kotlinx.coroutines.TestBase
import kotlinx.coroutines.flow.flow
import kotlinx.coroutines.flow.toList
import kotlinx.coroutines.withVirtualTime
import org.junit.Test
import java.time.Duration
import kotlin.test.assertEquals

class FlowSampleTest : TestBase() {
    @Test
    public fun testBasic() = withVirtualTime {
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
        val result = flow.sample(Duration.ofMillis(1000)).toList()
        assertEquals(listOf("A", "B", "D"), result)
        finish(5)
    }
}
