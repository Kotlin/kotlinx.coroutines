@file:JvmMultifileClass
@file:JvmName("ChannelsKt")
@file:Suppress("unused")

package kotlinx.coroutines.channels

import kotlinx.coroutines.*
import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * Opens subscription to this [BroadcastChannel] and makes sure that the given [block] consumes all elements
 * from it by always invoking [cancel][ReceiveChannel.cancel] after the execution of the block.
 *
 * **Note: This API is obsolete since 1.5.0 and deprecated for removal since 1.7.0**
 * It is replaced with [SharedFlow][kotlinx.coroutines.flow.SharedFlow].
 *
 * Safe to remove in 1.9.0 as was inline before.
 */
@ObsoleteCoroutinesApi
@Suppress("DEPRECATION_ERROR")
@Deprecated(level = DeprecationLevel.ERROR, message = "BroadcastChannel is deprecated in the favour of SharedFlow and is no longer supported")
public inline fun <E, R> BroadcastChannel<E>.consume(block: ReceiveChannel<E>.() -> R): R {
    val channel = openSubscription()
    try {
        return channel.block()
    } finally {
        channel.cancel()
    }
}

/**
 * Subscribes to this [BroadcastChannel] and performs the specified action for each received element.
 *
 * **Note: This API is obsolete since 1.5.0 and deprecated for removal since 1.7.0**
 */
@Deprecated(level = DeprecationLevel.ERROR, message = "BroadcastChannel is deprecated in the favour of SharedFlow and is no longer supported")
@Suppress("DEPRECATION", "DEPRECATION_ERROR")
public suspend inline fun <E> BroadcastChannel<E>.consumeEach(action: (E) -> Unit): Unit =
    consume {
        for (element in this) action(element)
    }

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
                    exception.addSuppressed(e)
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

/**
 * Deprecated version of [produce] that accepts a [Job].
 *
 * See the documentation for the non-deprecated [produce] function to learn about the functionality of this function.
 * This piece of documentation explains why this overload is deprecated.
 *
 * It is incorrect to pass a [Job] as [context] to [produce], [async], or [launch],
 * because this violates structured concurrency.
 * The passed [Job] becomes the sole parent of the newly created coroutine, which completely severs the tie between
 * the new coroutine and the [CoroutineScope] in which it is launched.
 *
 * Structured concurrency ensures that
 * - Cancellation of the parent job cancels the children as well,
 *   which helps avoid unnecessary computations when they are no longer needed.
 * - Cancellation of children also can be necessary for reliability:
 *   if the [CoroutineScope]'s lifecycle is bound to some component that may not be used after it's destroyed,
 *   performing computations after the parent [CoroutineScope] is cancelled may lead to crashes.
 * - For concurrent decomposition of work (when the [CoroutineScope] contains a non-[supervisor][SupervisorJob] job),
 *   failure of the newly created coroutine also causes the sibling coroutines to fail,
 *   improving the responsiveness of the program:
 *   unnecessary computations will not proceed when it's obvious that they are not needed.
 * - The [CoroutineScope] can only complete when all its children complete.
 *   If the [CoroutineScope] is lexically scoped (for example, created by [coroutineScope], [supervisorScope],
 *   or [withContext]), this means that
 *   the lexical scope will only be exited (and the calling function will finish) once all child coroutines complete.
 *
 * ## Possible alternatives
 *
 * ### Avoiding cancellation
 *
 * Sometimes, it is undesirable for the child coroutine to react to the cancellation of the parent: for example,
 * some computations have to be performed either way.
 * `produce(NonCancellable)` or `produce(Job())` can be used to achieve this effect.
 *
 * Alternative approaches that preserve structured concurrency are this:
 *
 * ```
 * // Guarantees the completion
 * scope.produce(start = CoroutineStart.ATOMIC) {
 *     withContext(NonCancellable) {
 *         // this line will be reached even if the parent is cancelled
 *     }
 * }
 * ```
 *
 * This way, the child coroutine is guaranteed to complete,
 * but the scope is still aware of the child and can track its lifecycle.
 *
 * ### Avoid cancelling other children
 *
 * Occasionally, the failure of one child does not mean the work of the other children is also unneeded.
 * `producer(Job()) { failure() }` makes sure that the only effect of `failure()` is to make *this* `producer` finish
 * with an error, while the other coroutines continue executing.
 *
 * If *all* coroutines in a scope should fail independently, this suggests that the scope
 * is a [*supervisor*][supervisorScope]:
 *
 * ```
 * supervisorScope {
 *     val producers = List(10) {
 *         produce<Int> {
 *             delay(10.milliseconds * it)
 *             throw IllegalStateException("$it is tired of all this")
 *         }
 *     }
 *     producers.forEach {
 *         println(runCatching { it.receive() })
 *     }
 * }
 * ```
 *
 * Every coroutine here will run to completion and will fail with its own error.
 *
 * For non-lexically-scoped [CoroutineScope] instances,
 * use [SupervisorJob] instead of [Job] when constructing the [CoroutineScope].
 *
 * If only *some* coroutines need to individually have their failures invisible to others
 * in a non-lexically-scoped [CoroutineScope],
 * the correct approach from the point of view of structured concurrency is this:
 *
 * ```
 * val childSupervisorScope = CoroutineScope(
 *     scope.coroutineContext + SupervisorJob(scope.coroutineContext.job)
 * )
 * childSupervisorScope.produce {
 *     // failures in this coroutine will not affect other children
 * }
 * ```
 *
 * For a lexically scoped [CoroutineScope], using a [supervisorScope] at the end of the outer scope may help:
 *
 * ```
 * coroutineScope {
 *     launch {
 *         // failures in this coroutine will affect everyone
 *     }
 *     supervisorScope {
 *         val channel = produce {
 *             // failures in this coroutine
 *             // are only available through `channel`
 *         }
 *     }
 *     // this line will only be reached when the `produce` coroutine complete
 * }
 * // this line will be reached when both `launch` and `produce` complete
 * ```
 *
 * All of these approaches preserve the ability of a parent to cancel the children and to wait for their completion.
 *
 * ### Avoiding both cancelling and being cancelled
 *
 * Sometimes, coroutines to be spawned are just completely unrelated to the [CoroutineScope] used as the receiver,
 * and no structured concurrency mechanisms are needed.
 *
 * In that case, [GlobalScope] is the semantically clearer way of expressing opting out of structured concurrency:
 *
 * ```
 * GlobalScope.produce {
 *     // this is explicitly a rogue computation
 * }
 * ```
 *
 * The reason why [GlobalScope] is marked as [delicate][DelicateCoroutinesApi] is exactly that the coroutines
 * created in it are outside structured concurrency.
 */
@Deprecated(
    "Passing a Job to coroutine builders breaks structured concurrency, leading to hard-to-diagnose errors. " +
        "This pattern should be avoided. " +
        "This overload will be deprecated with an error in the future.",
    level = DeprecationLevel.WARNING)
public fun <E> CoroutineScope.produce(
    context: Job,
    capacity: Int = Channel.RENDEZVOUS,
    @BuilderInference block: suspend ProducerScope<E>.() -> Unit
): ReceiveChannel<E> =
    produce(context as CoroutineContext, capacity, block)
