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

import kotlin.test.*


class BroadcastChannelFactoryTest {

    @Test
    fun testRendezvousChannelNotSupported() {
        assertFailsWith<IllegalArgumentException> { BroadcastChannel<Int>(0) }
    }

    @Test
    fun testLinkedListChannelNotSupported() {
        assertFailsWith<IllegalArgumentException> { BroadcastChannel<Int>(Channel.UNLIMITED) }
    }

    @Test
    fun testConflatedBroadcastChannel() {
        assertTrue { BroadcastChannel<Int>(Channel.CONFLATED) is ConflatedBroadcastChannel }
    }

    @Test
    fun testArrayBroadcastChannel() {
        assertTrue { BroadcastChannel<Int>(1) is ArrayBroadcastChannel }
        assertTrue { BroadcastChannel<Int>(10) is ArrayBroadcastChannel }
    }

    @Test
    fun testInvalidCapacityNotSupported() {
        assertFailsWith<IllegalArgumentException> { BroadcastChannel<Int>(-2) }
    }
}
