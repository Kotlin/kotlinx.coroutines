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

enum class TestBroadcastChannelKind {
    ARRAY_1 {
        override fun <T> create(): BroadcastChannel<T> = ArrayBroadcastChannel<T>(1)
        override fun toString(): String = "ArrayBroadcastChannel(1)"
    },
    ARRAY_10 {
        override fun <T> create(): BroadcastChannel<T> = ArrayBroadcastChannel<T>(10)
        override fun toString(): String = "ArrayBroadcastChannel(10)"
    },
    CONFLATED {
        override fun <T> create(): BroadcastChannel<T> = ConflatedBroadcastChannel<T>()
        override fun toString(): String = "ConflatedBroadcastChannel"
        override val isConflated: Boolean get() = true
    }
    ;

    abstract fun <T> create(): BroadcastChannel<T>
    open val isConflated: Boolean get() = false
}