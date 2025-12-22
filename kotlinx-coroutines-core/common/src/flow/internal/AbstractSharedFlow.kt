package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.channels.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.jvm.*

@JvmField
internal val EMPTY_RESUMES = arrayOfNulls<Continuation<Unit>?>(0)

/**
 * A slot occupied by a collector when it subscribes to a shared flow and freed when the collector unsubscribes.
 */
internal abstract class AbstractSharedFlowSlot<F> {
    /**
     * Try marking this slot as occupied by the given [flow]. Only call this under the [flow]'s lock.
     *
     * Returns `false` if the slot is already occupied by some other collector.
     */
    abstract fun occupyLocked(flow: F): Boolean

    /**
     * Stop occupying this slot, making it available for reuse. Only call this under the [flow]'s lock.
     *
     * Returns an array of continuations that need to be resumed after the lock is released.
     * These continuations represent suspended emitters that were waiting for the slowest collector to move on
     * so that their values can be placed into the buffer.
     */
    abstract fun leaveLocked(flow: F): Array<Continuation<Unit>?>
}

/**
 * A common data structure for `StateFlow` and `SharedFlow`.
 */
internal abstract class AbstractSharedFlow<SpecificImpl, S : AbstractSharedFlowSlot<SpecificImpl>>: SynchronizedObject()
{
    /**
     * Array of slots for collectors of the shared flow.
     *
     * `null` by default, created on demand.
     * Each cell is also `null` by default, and the specific slot object is [created][createSlot] on demand.
     * The whole array being `null` or a cell being `null` is equivalent to the cell not being
     * [occupied][AbstractSharedFlowSlot.occupyLocked].
     */
    protected var slots: Array<S?>? = null
        private set

    /**
     * The number of [occupied][AbstractSharedFlowSlot.occupyLocked] slots in [slots].
     */
    protected var nCollectors = 0
        private set

    /**
     * It is likely that the next non-occupied slot in [slots] will be at this index or to its right.
     *
     * It is not guaranteed that this slot will not be occupied, nor is it guaranteed that it will be the first
     * non-occupied slot.
     * This is just a heuristic to have a better guess in common scenarios.
     */
    private var nextIndex = 0

    /**
     * The backing field for [subscriptionCount].
     *
     * Will not be initialized until [subscriptionCount] is accessed for the first time.
     */
    private var _subscriptionCount: SubscriptionCountStateFlow? = null

    /** A `StateFlow` representing [nCollectors], potentially with some delay. A user-visible API. */
    val subscriptionCount: StateFlow<Int>
        get() = synchronized(this) {
            // allocate under lock in sync with nCollectors variable
            _subscriptionCount ?: SubscriptionCountStateFlow(nCollectors).also {
                _subscriptionCount = it
            }
        }

    /** Create a new implementation-specific representation of a collector, but do not place it in [slots] yet. */
    protected abstract fun createSlot(): S

    /** Equivalent to [arrayOfNulls]. */
    protected abstract fun createSlotArray(size: Int): Array<S?>

    /**
     * Have a new collector occupy some slot.
     *
     * A slot may be either [created][createSlot] or reused.
     */
    protected fun allocateSlot(): S {
        // Actually occupy slot under lock
        val subscriptionCount: SubscriptionCountStateFlow?
        val slot = synchronized(this) {
            val slots = when (val curSlots = slots) {
                null -> createSlotArray(2).also { slots = it }
                else -> if (nCollectors >= curSlots.size) {
                    curSlots.copyOf(2 * curSlots.size).also { slots = it }
                } else {
                    curSlots
                }
            }
            var index = nextIndex
            var slot: S
            while (true) {
                slot = slots[index] ?: createSlot().also { slots[index] = it }
                index++
                if (index >= slots.size) index = 0
                @Suppress("UNCHECKED_CAST")
                if (slot.occupyLocked(this as SpecificImpl)) break // break when found and occupied a free slot
            }
            nextIndex = index
            nCollectors++
            subscriptionCount = _subscriptionCount // retrieve under lock if initialized
            slot
        }
        // increments subscription count
        subscriptionCount?.increment(1)
        return slot
    }

    /** Have a collector no longer occupy its slot, making the latter available for reuse. */
    protected fun leaveSlot(slot: S) {
        // Release slot under lock
        val subscriptionCount: SubscriptionCountStateFlow?
        val resumes = synchronized(this) {
            nCollectors--
            subscriptionCount = _subscriptionCount // retrieve under lock if initialized
            // Reset next index hint if we have no more active collectors for more predictable behavior next time
            if (nCollectors == 0) nextIndex = 0
            @Suppress("UNCHECKED_CAST")
            slot.leaveLocked(this as SpecificImpl)
        }
        /*
         * Resume suspended coroutines.
         * This can happen when the subscriber that left was a slow one and was holding up buffer.
         * When this subscriber left, previously queued emitted can now wake up and are resumed here.
         */
        for (cont in resumes) cont?.resume(Unit)
        // decrement subscription count
        subscriptionCount?.increment(-1)
    }

    protected inline fun forEachSlotLocked(block: (S) -> Unit) {
        if (nCollectors == 0) return
        slots?.forEach { slot ->
            if (slot != null) block(slot)
        }
    }
}

/**
 * [StateFlow] that represents the number of subscriptions.
 *
 * It is exposed as a regular [StateFlow] in our public API, but it is implemented as [SharedFlow] undercover to
 * avoid conflations of consecutive updates because the subscription count is very sensitive to it.
 *
 * The importance of non-conflating can be demonstrated with the following example:
 * ```
 * val shared = flowOf(239).stateIn(this, SharingStarted.Lazily, 42) // stateIn for the sake of the initial value
 * println(shared.first())
 * yield()
 * println(shared.first())
 * ```
 * If the flow is shared within the same dispatcher (e.g. Main) or with a slow/throttled one,
 * the `SharingStarted.Lazily` will never be able to start the source: `first` sees the initial value and immediately
 * unsubscribes, leaving the asynchronous `SharingStarted` with conflated zero.
 *
 * To avoid that (especially in a more complex scenarios), we do not conflate subscription updates.
 */
@OptIn(ExperimentalForInheritanceCoroutinesApi::class)
private class SubscriptionCountStateFlow(initialValue: Int) : StateFlow<Int>,
    SharedFlowImpl<Int>(1, Int.MAX_VALUE, BufferOverflow.DROP_OLDEST)
{
    init { tryEmit(initialValue) }

    override val value: Int
        get() = synchronized(this) { lastReplayedLocked }

    fun increment(delta: Int) = synchronized(this) {
        tryEmit(lastReplayedLocked + delta)
    }
}
