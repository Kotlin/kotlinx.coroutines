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

internal const val DEFAULT_CLOSE_MESSAGE = "Channel was closed"

/**
 * Performs the given [action] for each received element.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <E> ReceiveChannel<E>.consumeEach(action: suspend (E) -> Unit) {
    for (element in this) action(element)
}

/**
 * Subscribes to this [BroadcastChannel] and performs the specified action for each received element.
 */
// :todo: make it inline when this bug is fixed: https://youtrack.jetbrains.com/issue/KT-16448
public suspend fun <E> BroadcastChannel<E>.consumeEach(action: suspend (E) -> Unit) {
    open().use { channel ->
        for (x in channel) action(x)
    }
}

/**
 * Collects all received elements into a [List].
 */
public suspend fun <E> ReceiveChannel<E>.collectList(): List<E> {
    val list = mutableListOf<E>()

    consumeEach { list += it }

    return list
}

/**
 * Collects all received elements into a [Map] using specified [keyExtractor] to extract key from element.
 */
public suspend fun <K, E> ReceiveChannel<E>.collectMap(keyExtractor: (E) -> K): Map<K, E> {
    val map = mutableMapOf<K, E>()

    consumeEach { map += keyExtractor(it) to it }

    return map
}

/**
 * Collects all received elements into a [Sequence].
 */
public suspend fun <E> ReceiveChannel<E>.collectSequence(): Sequence<E> = collectList().asSequence()

/**
 * Collects all received elements into a [Set].
 */
public suspend fun <E> ReceiveChannel<E>.collectSet(): Set<E> {
    val set = mutableSetOf<E>()

    consumeEach { set += it }

    return set
}

