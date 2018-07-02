/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.channels

enum class TestBroadcastChannelKind {
    ARRAY_1 {
        override fun <T> create(): BroadcastChannel<T> = ArrayBroadcastChannel(1)
        override fun toString(): String = "ArrayBroadcastChannel(1)"
    },
    ARRAY_10 {
        override fun <T> create(): BroadcastChannel<T> = ArrayBroadcastChannel(10)
        override fun toString(): String = "ArrayBroadcastChannel(10)"
    },
    CONFLATED {
        override fun <T> create(): BroadcastChannel<T> = ConflatedBroadcastChannel()
        override fun toString(): String = "ConflatedBroadcastChannel"
        override val isConflated: Boolean get() = true
    }
    ;

    abstract fun <T> create(): BroadcastChannel<T>
    open val isConflated: Boolean get() = false
}