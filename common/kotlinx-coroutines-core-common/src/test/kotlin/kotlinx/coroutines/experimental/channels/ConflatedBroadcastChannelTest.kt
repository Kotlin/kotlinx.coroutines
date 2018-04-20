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

class ConflatedBroadcastChannelTest : TestBase() {

    @Test
    fun testBasicScenario() = runTest {
        expect(1)
        val broadcast = ConflatedBroadcastChannel<String>()
        assertTrue(exceptionFromNotInline { broadcast.value } is IllegalStateException)
        assertNull(broadcast.valueOrNull)

        launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
            expect(2)
            val sub = broadcast.openSubscription()
            assertNull(sub.poll())
            expect(3)
            assertEquals("one", sub.receive()) // suspends
            expect(6)
            assertEquals("two", sub.receive()) // suspends
            expect(12)
            sub.close()
            expect(13)
        }

        expect(4)
        broadcast.send("one") // does not suspend
        assertEquals("one", broadcast.value)
        assertEquals("one", broadcast.valueOrNull)
        expect(5)
        yield() // to receiver
        expect(7)
        launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
            expect(8)
            val sub = broadcast.openSubscription()
            assertEquals("one", sub.receive()) // does not suspend
            expect(9)
            assertEquals("two", sub.receive()) // suspends
            expect(14)
            assertEquals("three", sub.receive()) // suspends
            expect(17)
            assertNull(sub.receiveOrNull()) // suspends until closed
            expect(20)
            sub.close()
            expect(21)
        }

        expect(10)
        broadcast.send("two") // does not suspend
        assertEquals("two", broadcast.value)
        assertEquals("two", broadcast.valueOrNull)
        expect(11)
        yield() // to both receivers
        expect(15)
        broadcast.send("three") // does not suspend
        assertEquals("three", broadcast.value)
        assertEquals("three", broadcast.valueOrNull)
        expect(16)
        yield() // to second receiver
        expect(18)
        broadcast.close()
        assertTrue(exceptionFromNotInline { broadcast.value } is IllegalStateException)
        assertNull(broadcast.valueOrNull)
        expect(19)
        yield() // to second receiver
        assertTrue(exceptionFrom { broadcast.send("four") } is ClosedSendChannelException)
        finish(22)
    }

    @Test
    fun testInitialValueAndReceiveClosed() = runTest {
        expect(1)
        val broadcast = ConflatedBroadcastChannel(1)
        assertEquals(1, broadcast.value)
        assertEquals(1, broadcast.valueOrNull)
        launch(coroutineContext, CoroutineStart.UNDISPATCHED) {
            expect(2)
            val sub = broadcast.openSubscription()
            assertEquals(1, sub.receive())
            expect(3)
            assertTrue(exceptionFrom { sub.receive() } is ClosedReceiveChannelException) // suspends
            expect(6)
        }
        expect(4)
        broadcast.close()
        expect(5)
        yield() // to child
        finish(7)
    }

    inline fun exceptionFrom(block: () -> Unit): Throwable? {
        try {
            block()
            return null
        } catch (e: Throwable) {
            return e
        }
    }

    // Ugly workaround for bug in JS compiler
    fun exceptionFromNotInline(block: () -> Unit): Throwable? {
        try {
            block()
            return null
        } catch (e: Throwable) {
            return e
        }
    }
}
