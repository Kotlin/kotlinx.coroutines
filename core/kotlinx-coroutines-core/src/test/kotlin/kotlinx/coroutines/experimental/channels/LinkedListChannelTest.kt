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
import kotlinx.coroutines.experimental.runBlocking
import org.hamcrest.MatcherAssert.assertThat
import org.hamcrest.core.IsEqual
import org.hamcrest.core.IsNull
import org.junit.Test

class LinkedListChannelTest : TestBase() {
    @Test
    fun testBasic() = runBlocking {
        val c = LinkedListChannel<Int>()
        c.send(1)
        check(c.offer(2))
        c.send(3)
        check(c.close())
        check(!c.close())
        assertThat(c.receive(), IsEqual(1))
        assertThat(c.poll(), IsEqual(2))
        assertThat(c.receiveOrNull(), IsEqual(3))
        assertThat(c.receiveOrNull(), IsNull())
    }

    @Test
    fun testConsumeAll() = runBlocking {
        val q = LinkedListChannel<Int>()
        for (i in 1..10) {
            q.send(i) // buffers
        }
        q.cancel()
        check(q.isClosedForSend)
        check(q.isClosedForReceive)
        check(q.receiveOrNull() == null)
    }
}