/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:JvmMultifileClass
@file:JvmName("ChannelsKt")
@file:Suppress("unused")

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.jvm.*

/** @suppress **/
@PublishedApi // Binary compatibility
internal fun consumesAll(vararg channels: ReceiveChannel<*>): CompletionHandler =
    { cause: Throwable? ->
        var exception: Throwable? = null
        for (channel in channels)
            try {
                channel.cancelConsumed(cause)
            } catch (e: Throwable) {
                if (exception == null) {
                    exception = e
                } else {
                    exception.addSuppressedThrowable(e)
                }
            }
        exception?.let { throw it }
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.elementAt(index: Int): E = consume {
    if (index < 0)
        throw IndexOutOfBoundsException("ReceiveChannel doesn't contain element at index $index.")
    var count = 0
    for (element in this) {
        @Suppress("UNUSED_CHANGED_VALUE") // KT-47628
        if (index == count++)
            return element
    }
    throw IndexOutOfBoundsException("ReceiveChannel doesn't contain element at index $index.")
}

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.elementAtOrNull(index: Int): E? =
    consume {
        if (index < 0)
            return null
        var count = 0
        for (element in this) {
            if (index == count++)
                return element
        }
        return null
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.first(): E =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext())
            throw NoSuchElementException("ReceiveChannel is empty.")
        return iterator.next()
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.firstOrNull(): E? =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext())
            return null
        return iterator.next()
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.indexOf(element: E): Int {
    var index = 0
    consumeEach {
        if (element == it)
            return index
        index++
    }
    return -1
}

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.last(): E =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext())
            throw NoSuchElementException("ReceiveChannel is empty.")
        var last = iterator.next()
        while (iterator.hasNext())
            last = iterator.next()
        return last
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.lastIndexOf(element: E): Int {
    var lastIndex = -1
    var index = 0
    consumeEach {
        if (element == it)
            lastIndex = index
        index++
    }
    return lastIndex
}

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.lastOrNull(): E? =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext())
            return null
        var last = iterator.next()
        while (iterator.hasNext())
            last = iterator.next()
        return last
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.single(): E =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext())
            throw NoSuchElementException("ReceiveChannel is empty.")
        val single = iterator.next()
        if (iterator.hasNext())
            throw IllegalArgumentException("ReceiveChannel has more than one element.")
        return single
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.singleOrNull(): E? =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext())
            return null
        val single = iterator.next()
        if (iterator.hasNext())
            return null
        return single
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> ReceiveChannel<E>.drop(n: Int, context: CoroutineContext = Dispatchers.Unconfined): ReceiveChannel<E> =
    GlobalScope.produce(context, onCompletion = consumes()) {
        require(n >= 0) { "Requested element count $n is less than zero." }
        var remaining: Int = n
        if (remaining > 0)
            for (e in this@drop) {
                remaining--
                if (remaining == 0)
                    break
            }
        for (e in this@drop) {
            send(e)
        }
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> ReceiveChannel<E>.dropWhile(
    context: CoroutineContext = Dispatchers.Unconfined,
    predicate: suspend (E) -> Boolean
): ReceiveChannel<E> =
    GlobalScope.produce(context, onCompletion = consumes()) {
        for (e in this@dropWhile) {
            if (!predicate(e)) {
                send(e)
                break
            }
        }
        for (e in this@dropWhile) {
            send(e)
        }
    }

@PublishedApi
internal fun <E> ReceiveChannel<E>.filter(
    context: CoroutineContext = Dispatchers.Unconfined,
    predicate: suspend (E) -> Boolean
): ReceiveChannel<E> =
    GlobalScope.produce(context, onCompletion = consumes()) {
        for (e in this@filter) {
            if (predicate(e)) send(e)
        }
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> ReceiveChannel<E>.filterIndexed(
    context: CoroutineContext = Dispatchers.Unconfined,
    predicate: suspend (index: Int, E) -> Boolean
): ReceiveChannel<E> =
    GlobalScope.produce(context, onCompletion = consumes()) {
        var index = 0
        for (e in this@filterIndexed) {
            if (predicate(index++, e)) send(e)
        }
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> ReceiveChannel<E>.filterNot(
    context: CoroutineContext = Dispatchers.Unconfined,
    predicate: suspend (E) -> Boolean
): ReceiveChannel<E> =
    filter(context) { !predicate(it) }

@PublishedApi
@Suppress("UNCHECKED_CAST")
internal fun <E : Any> ReceiveChannel<E?>.filterNotNull(): ReceiveChannel<E> =
    filter { it != null } as ReceiveChannel<E>

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E : Any, C : MutableCollection<in E>> ReceiveChannel<E?>.filterNotNullTo(destination: C): C {
    consumeEach {
        if (it != null) destination.add(it)
    }
    return destination
}

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E : Any, C : SendChannel<E>> ReceiveChannel<E?>.filterNotNullTo(destination: C): C {
    consumeEach {
        if (it != null) destination.send(it)
    }
    return destination
}

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> ReceiveChannel<E>.take(n: Int, context: CoroutineContext = Dispatchers.Unconfined): ReceiveChannel<E> =
    GlobalScope.produce(context, onCompletion = consumes()) {
        if (n == 0) return@produce
        require(n >= 0) { "Requested element count $n is less than zero." }
        var remaining: Int = n
        for (e in this@take) {
            send(e)
            remaining--
            if (remaining == 0)
                return@produce
        }
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> ReceiveChannel<E>.takeWhile(
    context: CoroutineContext = Dispatchers.Unconfined,
    predicate: suspend (E) -> Boolean
): ReceiveChannel<E> =
    GlobalScope.produce(context, onCompletion = consumes()) {
        for (e in this@takeWhile) {
            if (!predicate(e)) return@produce
            send(e)
        }
    }

@PublishedApi
internal suspend fun <E, C : SendChannel<E>> ReceiveChannel<E>.toChannel(destination: C): C {
    consumeEach {
        destination.send(it)
    }
    return destination
}

@PublishedApi
internal suspend fun <E, C : MutableCollection<in E>> ReceiveChannel<E>.toCollection(destination: C): C {
    consumeEach {
        destination.add(it)
    }
    return destination
}

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <K, V> ReceiveChannel<Pair<K, V>>.toMap(): Map<K, V> =
    toMap(LinkedHashMap())

@PublishedApi
internal suspend fun <K, V, M : MutableMap<in K, in V>> ReceiveChannel<Pair<K, V>>.toMap(destination: M): M {
    consumeEach {
        destination += it
    }
    return destination
}

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.toMutableList(): MutableList<E> =
    toCollection(ArrayList())

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.toSet(): Set<E> =
    this.toMutableSet()

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E, R> ReceiveChannel<E>.flatMap(
    context: CoroutineContext = Dispatchers.Unconfined,
    transform: suspend (E) -> ReceiveChannel<R>
): ReceiveChannel<R> =
    GlobalScope.produce(context, onCompletion = consumes()) {
        for (e in this@flatMap) {
            transform(e).toChannel(this)
        }
    }

@PublishedApi
internal fun <E, R> ReceiveChannel<E>.map(
    context: CoroutineContext = Dispatchers.Unconfined,
    transform: suspend (E) -> R
): ReceiveChannel<R> =
    GlobalScope.produce(context, onCompletion = consumes()) {
        consumeEach {
            send(transform(it))
        }
    }

@PublishedApi
internal fun <E, R> ReceiveChannel<E>.mapIndexed(
    context: CoroutineContext = Dispatchers.Unconfined,
    transform: suspend (index: Int, E) -> R
): ReceiveChannel<R> =
    GlobalScope.produce(context, onCompletion = consumes()) {
        var index = 0
        for (e in this@mapIndexed) {
            send(transform(index++, e))
        }
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E, R : Any> ReceiveChannel<E>.mapIndexedNotNull(
    context: CoroutineContext = Dispatchers.Unconfined,
    transform: suspend (index: Int, E) -> R?
): ReceiveChannel<R> =
    mapIndexed(context, transform).filterNotNull()

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E, R : Any> ReceiveChannel<E>.mapNotNull(
    context: CoroutineContext = Dispatchers.Unconfined,
    transform: suspend (E) -> R?
): ReceiveChannel<R> =
    map(context, transform).filterNotNull()

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> ReceiveChannel<E>.withIndex(context: CoroutineContext = Dispatchers.Unconfined): ReceiveChannel<IndexedValue<E>> =
    GlobalScope.produce(context, onCompletion = consumes()) {
        var index = 0
        for (e in this@withIndex) {
            send(IndexedValue(index++, e))
        }
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E> ReceiveChannel<E>.distinct(): ReceiveChannel<E> =
    this.distinctBy { it }

@PublishedApi
internal fun <E, K> ReceiveChannel<E>.distinctBy(
    context: CoroutineContext = Dispatchers.Unconfined,
    selector: suspend (E) -> K
): ReceiveChannel<E> =
    GlobalScope.produce(context, onCompletion = consumes()) {
        val keys = HashSet<K>()
        for (e in this@distinctBy) {
            val k = selector(e)
            if (k !in keys) {
                send(e)
                keys += k
            }
        }
    }

@PublishedApi
internal suspend fun <E> ReceiveChannel<E>.toMutableSet(): MutableSet<E> =
    toCollection(LinkedHashSet())

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.any(): Boolean =
    consume {
        return iterator().hasNext()
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.count(): Int {
    var count = 0
    consumeEach { count++ }
    return count
}

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.maxWith(comparator: Comparator<in E>): E? =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext()) return null
        var max = iterator.next()
        while (iterator.hasNext()) {
            val e = iterator.next()
            if (comparator.compare(max, e) < 0) max = e
        }
        return max
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.minWith(comparator: Comparator<in E>): E? =
    consume {
        val iterator = iterator()
        if (!iterator.hasNext()) return null
        var min = iterator.next()
        while (iterator.hasNext()) {
            val e = iterator.next()
            if (comparator.compare(min, e) > 0) min = e
        }
        return min
    }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public suspend fun <E> ReceiveChannel<E>.none(): Boolean =
    consume {
        return !iterator().hasNext()
    }

/** @suppress **/
@Deprecated(message = "Left for binary compatibility", level = DeprecationLevel.HIDDEN)
public fun <E : Any> ReceiveChannel<E?>.requireNoNulls(): ReceiveChannel<E> =
    map { it ?: throw IllegalArgumentException("null element found in $this.") }

/** @suppress **/
@Deprecated(message = "Binary compatibility", level = DeprecationLevel.HIDDEN)
public infix fun <E, R> ReceiveChannel<E>.zip(other: ReceiveChannel<R>): ReceiveChannel<Pair<E, R>> =
    zip(other) { t1, t2 -> t1 to t2 }

@PublishedApi // Binary compatibility
internal fun <E, R, V> ReceiveChannel<E>.zip(
    other: ReceiveChannel<R>,
    context: CoroutineContext = Dispatchers.Unconfined,
    transform: (a: E, b: R) -> V
): ReceiveChannel<V> =
    GlobalScope.produce(context, onCompletion = consumesAll(this, other)) {
        val otherIterator = other.iterator()
        this@zip.consumeEach { element1 ->
            if (!otherIterator.hasNext()) return@consumeEach
            val element2 = otherIterator.next()
            send(transform(element1, element2))
        }
    }

@PublishedApi // Binary compatibility
internal fun ReceiveChannel<*>.consumes(): CompletionHandler = { cause: Throwable? ->
    cancelConsumed(cause)
}
