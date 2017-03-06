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

enum class TestChannelKind {
    RENDEZVOUS {
        override fun create(): Channel<Int> = RendezvousChannel<Int>()
        override fun toString(): String = "RendezvousChannel"
    },
    ARRAY_1 {
        override fun create(): Channel<Int> = ArrayChannel<Int>(1)
        override fun toString(): String = "ArrayChannel(1)"
    },
    ARRAY_10 {
        override fun create(): Channel<Int> = ArrayChannel<Int>(8)
        override fun toString(): String = "ArrayChannel(8)"
    },
    LINKED_LIST {
        override fun create(): Channel<Int> = LinkedListChannel<Int>()
        override fun toString(): String = "LinkedListChannel"
    },
    CONFLATED {
        override fun create(): Channel<Int> = ConflatedChannel<Int>()
        override fun toString(): String = "ConflatedChannel"
    }
    ;

    abstract fun create(): Channel<Int>
}
