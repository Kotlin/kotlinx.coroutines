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
import org.hamcrest.core.IsInstanceOf
import org.hamcrest.core.IsNull
import org.junit.Assert.*
import org.junit.Test

class ValueBroadcastChannelTest : TestBase() {
    @Test
    fun testBasicScenario() = runBlocking {
        expect(1)
        val broadcast = ValueBroadcastChannel<String>()
        assertThat(exceptionFrom { broadcast.value }, IsInstanceOf(IllegalStateException::class.java))
        assertThat(broadcast.valueOrNull, IsNull())
        launch(context, CoroutineStart.UNDISPATCHED) {
            expect(2)
            val sub = broadcast.open()
            assertThat(sub.poll(), IsNull())
            expect(3)
            assertThat(sub.receive(), IsEqual("one")) // suspends
            expect(6)
            assertThat(sub.receive(), IsEqual("two")) // suspends
            expect(12)
            sub.close()
            expect(13)
        }
        expect(4)
        broadcast.send("one") // does not suspend
        assertThat(broadcast.value, IsEqual("one"))
        assertThat(broadcast.valueOrNull, IsEqual("one"))
        expect(5)
        yield() // to receiver
        expect(7)
        launch(context, CoroutineStart.UNDISPATCHED) {
            expect(8)
            val sub = broadcast.open()
            assertThat(sub.receive(), IsEqual("one")) // does not suspend
            expect(9)
            assertThat(sub.receive(), IsEqual("two")) // suspends
            expect(14)
            assertThat(sub.receive(), IsEqual("three")) // suspends
            expect(17)
            assertThat(sub.receiveOrNull(), IsNull()) // suspends until closed
            expect(20)
            sub.close()
            expect(21)
        }
        expect(10)
        broadcast.send("two") // does not suspend
        assertThat(broadcast.value, IsEqual("two"))
        assertThat(broadcast.valueOrNull, IsEqual("two"))
        expect(11)
        yield() // to both receivers
        expect(15)
        broadcast.send("three") // does not suspend
        assertThat(broadcast.value, IsEqual("three"))
        assertThat(broadcast.valueOrNull, IsEqual("three"))
        expect(16)
        yield() // to second receiver
        expect(18)
        broadcast.close()
        assertThat(exceptionFrom { broadcast.value }, IsInstanceOf(IllegalStateException::class.java))
        assertThat(broadcast.valueOrNull, IsNull())
        expect(19)
        yield() // to second receiver
        assertThat(exceptionFrom { broadcast.send("four") }, IsInstanceOf(ClosedSendChannelException::class.java))
        finish(22)
    }

    @Test
    fun testInitialValueAndReceiveClosed() = runBlocking {
        expect(1)
        val broadcast = ValueBroadcastChannel<Int>(1)
        assertThat(broadcast.value, IsEqual(1))
        assertThat(broadcast.valueOrNull, IsEqual(1))
        launch(context, CoroutineStart.UNDISPATCHED) {
            expect(2)
            val sub = broadcast.open()
            assertThat(sub.receive(), IsEqual(1))
            expect(3)
            assertThat(exceptionFrom { sub.receive() }, IsInstanceOf(ClosedReceiveChannelException::class.java)) // suspends
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
}