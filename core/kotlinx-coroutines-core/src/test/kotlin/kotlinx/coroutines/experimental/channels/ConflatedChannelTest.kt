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

import kotlinx.coroutines.experimental.TestBase
import kotlinx.coroutines.experimental.launch
import kotlinx.coroutines.experimental.runBlocking
import kotlinx.coroutines.experimental.yield
import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsNull
import org.junit.Assert.assertThat
import org.junit.Test

class ConflatedChannelTest : TestBase() {
    @Test
    fun testBasicConflationOfferPoll() {
        val q = ConflatedChannel<Int>()
        assertThat(q.poll(), IsNull())
        assertThat(q.offer(1), IsEqual(true))
        assertThat(q.offer(2), IsEqual(true))
        assertThat(q.offer(3), IsEqual(true))
        assertThat(q.poll(), IsEqual(3))
        assertThat(q.poll(), IsNull())
    }

    @Test
    fun testConflatedSend() = runBlocking<Unit> {
        val q = ConflatedChannel<Int>()
        q.send(1)
        q.send(2) // shall conflated previously sent
        assertThat(q.receiveOrNull(), IsEqual(2))
    }

    @Test
    fun testConflatedClose() = runBlocking<Unit> {
        val q = ConflatedChannel<Int>()
        q.send(1)
        q.close() // shall conflate sent item and become closed
        assertThat(q.receiveOrNull(), IsNull())
    }

    @Test
    fun testConflationSendReceive() = runBlocking<Unit> {
        val q = ConflatedChannel<Int>()
        expect(1)
        launch(coroutineContext) { // receiver coroutine
            expect(4)
            assertThat(q.receive(), IsEqual(2))
            expect(5)
            assertThat(q.receive(), IsEqual(3)) // this receive suspends
            expect(8)
            assertThat(q.receive(), IsEqual(6)) // last conflated value
            expect(9)
        }
        expect(2)
        q.send(1)
        q.send(2) // shall conflate
        expect(3)
        yield() // to receiver
        expect(6)
        q.send(3) // send to the waiting receiver
        q.send(4) // buffer
        q.send(5) // conflate
        q.send(6) // conflate again
        expect(7)
        yield() // to receiver
        finish(10)
    }

    @Test
    fun testConsumeAll() = runBlocking {
        val q = ConflatedChannel<Int>()
        expect(1)
        for (i in 1..10) {
            q.send(i) // stores as last
        }
        q.cancel()
        check(q.isClosedForSend)
        check(q.isClosedForReceive)
        check(q.receiveOrNull() == null)
        finish(2)
    }
}