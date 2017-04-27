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
import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsNull
import org.junit.Assert.*
import org.junit.Test

class ArrayBroadcastChannelTest : TestBase() {
    @Test
    fun testBasic() = runBlocking<Unit> {
        expect(1)
        val broadcast = ArrayBroadcastChannel<Int>(1)
        assertThat(broadcast.isClosedForSend, IsEqual(false))
        val first = broadcast.open()
        launch(context, CoroutineStart.UNDISPATCHED) {
            expect(2)
            assertThat(first.receive(), IsEqual(1)) // suspends
            assertThat(first.isClosedForReceive, IsEqual(false))
            expect(5)
            assertThat(first.receive(), IsEqual(2)) // suspends
            assertThat(first.isClosedForReceive, IsEqual(false))
            expect(10)
            assertThat(first.receiveOrNull(), IsNull()) // suspends
            assertThat(first.isClosedForReceive, IsEqual(true))
            expect(14)
        }
        expect(3)
        broadcast.send(1)
        expect(4)
        yield() // to the first receiver
        expect(6)
        val second = broadcast.open()
        launch(context, CoroutineStart.UNDISPATCHED) {
            expect(7)
            assertThat(second.receive(), IsEqual(2)) // suspends
            assertThat(second.isClosedForReceive, IsEqual(false))
            expect(11)
            assertThat(second.receiveOrNull(), IsNull()) // suspends
            assertThat(second.isClosedForReceive, IsEqual(true))
            expect(15)
        }
        expect(8)
        broadcast.send(2)
        expect(9)
        yield() // to first & second receivers
        expect(12)
        broadcast.close()
        expect(13)
        assertThat(broadcast.isClosedForSend, IsEqual(true))
        yield() // to first & second receivers
        finish(16)
    }

    @Test
    fun testSendSuspend() = runBlocking {
        expect(1)
        val broadcast = ArrayBroadcastChannel<Int>(1)
        val first = broadcast.open()
        launch(context) {
            expect(4)
            assertThat(first.receive(), IsEqual(1))
            expect(5)
            assertThat(first.receive(), IsEqual(2))
            expect(6)
        }
        expect(2)
        broadcast.send(1) // puts to buffer, receiver not running yet
        expect(3)
        broadcast.send(2) // suspends
        finish(7)
    }

    @Test
    fun testConcurrentSendCompletion() = runBlocking {
        expect(1)
        val broadcast = ArrayBroadcastChannel<Int>(1)
        val sub = broadcast.open()
        // launch 3 concurrent senders (one goes buffer, two other suspend)
        for (x in 1..3) {
            launch(context, CoroutineStart.UNDISPATCHED) {
                expect(x + 1)
                broadcast.send(x)
            }
        }
        // and close it for send
        expect(5)
        broadcast.close()
        // now must receive all 3 items
        expect(6)
        assertThat(sub.isClosedForReceive, IsEqual(false))
        for (x in 1..3)
            assertThat(sub.receiveOrNull(), IsEqual(x))
        // and receive close signal
        assertThat(sub.receiveOrNull(), IsNull())
        assertThat(sub.isClosedForReceive, IsEqual(true))
        finish(7)
    }
}