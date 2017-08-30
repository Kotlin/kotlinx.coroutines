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

import org.hamcrest.MatcherAssert.assertThat
import org.hamcrest.core.IsInstanceOf
import org.junit.Test

class BroadcastChannelFactoryTest {
    @Test(expected = IllegalArgumentException::class)
    fun testRendezvousChannelNotSupported() {
        BroadcastChannel<Int>(0)
    }

    @Test(expected = IllegalArgumentException::class)
    fun testLinkedListChannelNotSupported() {
        BroadcastChannel<Int>(Channel.UNLIMITED)
    }

    @Test
    fun testConflatedBroadcastChannel() {
        assertThat(BroadcastChannel<Int>(Channel.CONFLATED), IsInstanceOf(ConflatedBroadcastChannel::class.java))
    }

    @Test
    fun testArrayBroadcastChannel() {
        assertThat(BroadcastChannel<Int>(1), IsInstanceOf(ArrayBroadcastChannel::class.java))
        assertThat(BroadcastChannel<Int>(10), IsInstanceOf(ArrayBroadcastChannel::class.java))
    }

    @Test(expected = IllegalArgumentException::class)
    fun testInvalidCapacityNotSupported() {
        BroadcastChannel<Int>(-2)
    }
}