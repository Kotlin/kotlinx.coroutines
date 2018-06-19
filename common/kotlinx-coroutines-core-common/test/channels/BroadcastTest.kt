/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental.channels

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*
import kotlin.test.*

class BroadcastTest : TestBase() {
    @Test
    fun testBroadcastBasic() = runTest {
        expect(1)
        val b = broadcast(coroutineContext) {
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