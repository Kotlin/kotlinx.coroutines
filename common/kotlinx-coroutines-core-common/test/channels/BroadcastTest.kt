/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class BroadcastTest : TestBase() {
    @Test
    fun testBroadcastBasic() = runTest {
        expect(1)
        val b = broadcast {
            expect(4)
            send(1) // goes to receiver
            expect(5)
            send(2) // goes to buffer
            expect(6)
            send(3) // suspends, will not be consumes, but will not be cancelled either
            expect(10)
        }
        yield() // has no effect, because default is lazy
        expect(2)
        b.consume {
            expect(3)
            assertEquals(1, receive()) // suspends
            expect(7)
            assertEquals(2, receive()) // suspends
            expect(8)
        }
        expect(9)
        yield() // to broadcast
        finish(11)
    }
}