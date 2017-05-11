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

class ChannelFactoryTest {
    @Test
    fun testRendezvousChannel() {
        assertThat(Channel<Int>(), IsInstanceOf(RendezvousChannel::class.java))
        assertThat(Channel<Int>(0), IsInstanceOf(RendezvousChannel::class.java))
    }

    @Test
    fun testLinkedListChannel() {
        assertThat(Channel<Int>(Channel.UNLIMITED), IsInstanceOf(LinkedListChannel::class.java))
    }

    @Test
    fun testConflatedChannel() {
        assertThat(Channel<Int>(Channel.CONFLATED), IsInstanceOf(ConflatedChannel::class.java))
    }

    @Test
    fun testArrayChannel() {
        assertThat(Channel<Int>(1), IsInstanceOf(ArrayChannel::class.java))
        assertThat(Channel<Int>(10), IsInstanceOf(ArrayChannel::class.java))
    }

    @Test(expected = IllegalArgumentException::class)
    fun testInvalidCapacityNotSupported() {
        Channel<Int>(-2)
    }
}