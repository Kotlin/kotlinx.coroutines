package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlin.coroutines.*
import kotlinx.coroutines.sync.*

/**
 * Constructs a [MultiplexFlow].
 *
 * Behavior:
 * * [getAll] is called every time the total keys collected by flows returned by [MultiplexFlow.get] changes (when collection is started or stopped).
 * * [getAll] is called with the total keys of all collected [MultiplexFlow.get] flows.
 * * [MultiplexFlow.get] calls share the data between them, such that [getAll] is not invoked when all the keys provided to [MultiplexFlow.get] are already collected by another [MultiplexFlow.get] caller.
 *   If [replay] is 0, this rule does not apply and [getAll] is re-invoked for every change in collections.
 * * Errors in calls to [getAll] trigger a rollback to the previous keys, and collections of all [MultiplexFlow.get] with one of the new keys will throw that error.
 * * Follow-up [getAll] error, or an error after the [getAll] collection already succeeded, will clear all subscriptions and cause all [MultiplexFlow.get] collections to throw that error.
 * * If the flow returned by [getAll] finishes, all current collections of [MultiplexFlow.get] finish as well, and follow-up collections will re-invoke [getAll].
 */
public fun <K, V> MultiplexFlow(
    scope: CoroutineScope,
    replay: Int = 1,
    extraBufferCapacity: Int = 0,
    onBufferOverflow: BufferOverflow = BufferOverflow.SUSPEND,
    getAll: suspend (keys: Set<K>) -> Flow<Map<K, V>>,
): MultiplexFlow<K, V> {
    return MultiplexFlow(
        Multiplexer(
            getAll, replay = replay, extraBufferCapacity = extraBufferCapacity, onBufferOverflow = onBufferOverflow
        ).launchIn(scope)
    )
}

/**
 * Allows multiplexing multiple subscriptions to a single [Flow].
 *
 * This is useful when the source allows only a single subscription, but the data is needed by
 * multiple users.
 */
public class MultiplexFlow<K, V> internal constructor(private val multiplexer: Multiplexer<K, V>) {
    /**
     * Returns a [Flow] that emits [V] for the requested [K]s, based on the map provided by
     * `getAll`.
     */
    public operator fun get(vararg keys: K): Flow<V> = flow {
        multiplexer.incrementUsage(*keys)
        try {
            multiplexer.values.filterKeys { it in keys }.values.merge().collectWhile {
                when (it) {
                    is Multiplexer.Value -> emit(it.value)
                    is Multiplexer.Error -> throw it.error
                    is Multiplexer.Finish -> return@collectWhile false
                }
                true
            }
        } finally {
            multiplexer.decrementUsage(*keys)
        }
    }
}

/** Internal implementation that multiplexes the data to [MultiplexFlow]. */
internal class Multiplexer<K, V>(
    private val getAll: suspend (keys: Set<K>) -> Flow<Map<K, V>>,
    private val replay: Int,
    private val extraBufferCapacity: Int,
    private val onBufferOverflow: BufferOverflow,
) {
    /** Current collected flows in [MultiplexFlow.get]. */
    private val subscriptions = MutableStateFlow(mapOf<K, Set<CoroutineContext>>())

    /** Current multiplexed values by key. */
    internal val values = mutableMapOf<K, MutableSharedFlow<Emitted<V>>>()

    private val valuesLock = Mutex()

    /** Last [subscriptions] keys, to know what changed. */
    private var lastUsedKeys = setOf<K>()

    /** Last [getAll] flow processor, so we can replace it with another. */
    private var lastFlowsProcessor: Job? = null

    /** Must only be called exactly once. */
    internal fun launchIn(scope: CoroutineScope): Multiplexer<K, V> = also {
        scope.launch {
            try {
                subscriptions.collect { current ->
                    val usedKeys = current.filterValues { it.isNotEmpty() }.keys
                    if (replay > 0 && usedKeys == lastUsedKeys) return@collect
                    lastFlowsProcessor?.cancel()
                    for (value in values.values) value.resetReplayCache()
                    if (usedKeys.isEmpty()) {
                        lastUsedKeys = usedKeys
                        return@collect
                    }
                    val flow = tryGetAll(usedKeys) ?: return@collect
                    lastUsedKeys = usedKeys
                    // Getting succeeded, processing the flow.
                    lastFlowsProcessor = launch { processFlow(usedKeys, flow) }
                }
            } finally {
                lastFlowsProcessor?.cancel()
                for (value in values.values) value.emit(Finish())
            }
        }
    }

    internal suspend fun incrementUsage(vararg keys: K) {
        // Creating SharedFlows if needed.
        valuesLock.withLock {
            for (key in keys) {
                if (values[key] == null) {
                    values[key] = MutableSharedFlow(
                        replay = replay, extraBufferCapacity = extraBufferCapacity, onBufferOverflow = onBufferOverflow
                    )
                }
            }
        }
        subscriptions.update { previous ->
            previous + keys.associateWith { (previous[it] ?: setOf()) + currentCoroutineContext() }
        }
    }

    internal suspend fun decrementUsage(vararg keys: K) {
        subscriptions.update { previous ->
            previous + keys.associateWith { (previous[it] ?: setOf()) - currentCoroutineContext() }
        }
    }

    /** Tries [getAll], rolling back and returning `null` on failure. */
    private suspend fun tryGetAll(keys: Set<K>): Flow<Map<K, V>>? = try {
        getAll(keys)
    } catch (e: CancellationException) {
        throw e
    } catch (e: Throwable) {
        // Failed to get, rolling back.
        rollbackSubscriptions(lastUsedKeys, e)
        lastUsedKeys = if (lastUsedKeys.isEmpty()) {
            keys // Forcing a change to clear the subscription.
        } else {
            setOf() // Prevent infinite retries.
        }
        null
    }

    /** Processes the flow returned by [getAll], updating [values] of each entry. */
    private suspend fun processFlow(keys: Set<K>, flow: Flow<Map<K, V>>) {
        try {
            flow.collect {
                for ((key, value) in it) {
                    if (key !in keys) continue // Ignoring keys that weren't subscribed.
                    values[key]!!.emit(Value(value))
                }
            }
        } catch (e: CancellationException) {
            throw e
        } catch (e: Throwable) {
            // Failed to collect, cancelling everything.
            rollbackSubscriptions(setOf(), e)
            return
        }
        for (value in values.values) {
            value.emit(Finish())
        }
    }

    /**
     * Rollbacks to `to` by removing the extras from [subscriptions] and setting the [values] of the
     * removed keys to the error provided in the `cause`.
     */
    private suspend fun rollbackSubscriptions(to: Set<K>, cause: Throwable) {
        // Filter only data types in previous.
        val from = subscriptions.getAndUpdate { previous -> previous.filter { (key, _) -> key in to } }
        // If they weren't, set their state the error.
        for (key in from.keys - to) {
            values[key]!!.emit(Error(cause))
        }
    }

    internal sealed interface Emitted<V>

    internal data class Value<V>(val value: V) : Emitted<V>

    internal data class Error<V>(val error: Throwable) : Emitted<V>

    internal class Finish<V> : Emitted<V>
}
