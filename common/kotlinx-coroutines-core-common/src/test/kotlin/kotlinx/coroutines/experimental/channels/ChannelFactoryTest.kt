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
import kotlin.test.*


class ChannelFactoryTest : TestBase() {

    @Test
    fun testRendezvousChannel() {
        assertTrue(Channel<Int>() is RendezvousChannel)
        assertTrue(Channel<Int>(0) is RendezvousChannel)
    }

    @Test
    fun testLinkedListChannel() {
        assertTrue(Channel<Int>(Channel.UNLIMITED) is LinkedListChannel)
    }

    @Test
    fun testConflatedChannel() {
        assertTrue(Channel<Int>(Channel.CONFLATED) is ConflatedChannel)
    }

    @Test
    fun testArrayChannel() {
        assertTrue(Channel<Int>(1) is ArrayChannel)
        assertTrue(Channel<Int>(10) is ArrayChannel)
    }

    @Test
    fun testInvalidCapacityNotSupported() = runTest({ it is IllegalArgumentException }) {
        Channel<Int>(-2)
    }
}
