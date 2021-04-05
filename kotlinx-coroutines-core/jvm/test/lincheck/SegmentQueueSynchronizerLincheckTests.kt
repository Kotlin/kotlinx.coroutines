/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused", "MemberVisibilityCanBePrivate")
package kotlinx.coroutines.lincheck

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.internal.SegmentQueueSynchronizer.CancellationMode.*
import kotlinx.coroutines.internal.SegmentQueueSynchronizer.ResumeMode.*
import kotlinx.coroutines.sync.Semaphore
import org.jetbrains.kotlinx.lincheck.*
import org.jetbrains.kotlinx.lincheck.annotations.*
import org.jetbrains.kotlinx.lincheck.annotations.Operation
import org.jetbrains.kotlinx.lincheck.strategy.managed.modelchecking.*
import org.jetbrains.kotlinx.lincheck.verifier.*
import java.util.concurrent.*
import kotlin.collections.ArrayList
import kotlin.coroutines.*
import kotlin.reflect.*

// This test suit serves two purposes. First of all, it tests the `SegmentQueueSynchronizer`
// implementation under different use-cases and workloads. On the other side, this test suite
// provides different well-known synchronization and communication primitive implementations
// via `SegmentQueueSynchronizer`, which can be considered as an API richness check as well as
// a collection of examples on how to use `SegmentQueueSynchronizer` to build new primitives.

// ##############
// # SEMAPHORES #
// ##############

/**
 * This [Semaphore] implementation is similar to the one in the library,
 * but uses the [asynchronous][ASYNC] resumption mode. However, it is non-trivial
 * to make [tryAcquire] linearizable in this case, so it is not supported here.
 */
internal class AsyncSemaphore(permits: Int) : SegmentQueueSynchronizer<Unit>(), Semaphore {
    override val resumeMode get() = ASYNC

    private val _availablePermits = atomic(permits)
    override val availablePermits get() = _availablePermits.value.coerceAtLeast(0)

    override fun tryAcquire() = error("Not implemented") // Not supported in the ASYNC version

    override suspend fun acquire() {
        // Decrement the number of available permits.
        val p = _availablePermits.getAndDecrement()
        // Is the permit successfully acquired?
        if (p > 0) return
        // Suspend otherwise.
        suspendCancellableCoroutine<Unit> { cont ->
            check(suspend(cont)) { "Should not fail in ASYNC mode" }
        }
    }

    override fun release() {
        while (true) {
            // Increment the number of available permits.
            val p = _availablePermits.getAndIncrement()
            // Is there a waiter that should be resumed?
            if (p >= 0) return
            // Try to resume the first waiter, and
            // restart the operation if it is cancelled.
            if (resume(Unit)) return
        }
    }

    // For prompt cancellation.
    override fun returnValue(value: Unit) = release()
}

/**
 * This semaphore implementation is correct only if [release] is always
 * invoked after a successful [acquire]; in other words, when semaphore
 * is used properly, without unexpected [release] invocations. The main
 * advantage is using smart cancellation, so [release] always works
 * in constant time under no contention, and the cancelled [acquire]
 * requests do not play any role. It is worth noting, that it is possible
 * to make this implementation correct under the prompt cancellation model
 * even with unexpected [release]-s.
 */
internal class AsyncSemaphoreSmart(permits: Int) : SegmentQueueSynchronizer<Unit>(), Semaphore {
    override val resumeMode get() = ASYNC
    override val cancellationMode get() = SMART

    private val _availablePermits = atomic(permits)
    override val availablePermits get() = _availablePermits.value.coerceAtLeast(0)

    override fun tryAcquire() = error("Not implemented") // Not supported in the ASYNC version.

    override suspend fun acquire() {
        // Decrement the number of available permits.
        val p = _availablePermits.getAndDecrement()
        // Is the permit acquired?
        if (p > 0) return
        // Suspend otherwise.
        suspendCancellableCoroutine<Unit> { cont ->
            check(suspend(cont)) { "Should not fail in ASYNC mode" }
        }
    }

    override fun release() {
        // Increment the number of available permits.
        val p = _availablePermits.getAndIncrement()
        // Is there a waiter that should be resumed?
        if (p >= 0) return
        // Resume the first waiter. Due to the smart
        // cancellation mode it is possible that this
        // permit will be refused, so this release
        // invocation can take effect with a small lag
        // and with an extra suspension, but it is guaranteed
        // that the permit will be refused eventually.
        resume(Unit)
    }

    override fun onCancellation(): Boolean {
        // Increment the number of available permits.
        val p = _availablePermits.getAndIncrement()
        // Return `true` if there is no `release` that
        // is going to resume this cancelling `acquire()`,
        // or `false` if there is one, and this permit
        // should be refused.
        return p < 0
    }

    // For prompt cancellation.
    override fun returnValue(value: Unit) = release()
}

/**
 * This implementation is similar to the previous one, but with [synchronous][SYNC]
 * resumption mode, so it is possible to implement [tryAcquire] correctly.
 * The only notable difference happens when a permit to be released is refused,
 * and the following [resume] attempt in the cancellation handler fails due to
 * the synchronization on resumption, so the permit is going to be returned
 * back to the semaphore in [returnValue] function. It is worth noting, that it
 * is possible to make this implementation correct with prompt cancellation.
 */
internal class SyncSemaphoreSmart(permits: Int) : SegmentQueueSynchronizer<Boolean>(), Semaphore {
    override val resumeMode get() = SYNC
    override val cancellationMode get() = SMART

    private val _availablePermits = atomic(permits)
    override val availablePermits get() = _availablePermits.value.coerceAtLeast(0)

    override suspend fun acquire() {
        while (true) {
            // Decrement the number of available permits.
            val p = _availablePermits.getAndDecrement()
            // Is the permit acquired?
            if (p > 0) return
            // Try to suspend otherwise.
            val acquired = suspendCancellableCoroutine<Boolean> { cont ->
                if (!suspend(cont)) cont.resume(false)
            }
            if (acquired) return
        }
    }

    override fun tryAcquire(): Boolean = _availablePermits.loop { cur ->
        // Try to decrement the number of available
        // permits if it is greater than zero.
        if (cur <= 0) return false
        if (_availablePermits.compareAndSet(cur, cur -1)) return true
    }

    override fun release() {
        while (true) {
            // Increment the number of available permits.
            val p = _availablePermits.getAndIncrement()
            // Is there a waiter that should be resumed?
            if (p >= 0) return
            // Try to resume the first waiter, can fail
            // according to the SYNC mode contract.
            if (resume(true)) return
        }
    }

    override fun onCancellation(): Boolean {
        // Increment the number of available permits.
        val p = _availablePermits.getAndIncrement()
        // Return `true` if there is no `release` which
        // is going to resume us and cannot skip us and
        // resume the next waiter.
        return p < 0
    }

    override fun returnValue(value: Boolean) {
        // Simply release the permit.
        release()
    }
}

class SemaphoreUnboundedSequential1 : SemaphoreSequential(1, false)
class SemaphoreUnboundedSequential2 : SemaphoreSequential(2, false)

// Comparing to `SemaphoreLincheckTestBase`, it does not support `tryAcquire()`.
abstract class AsyncSemaphoreLincheckTestBase(
    semaphore: Semaphore,
    private val seqSpec: KClass<*>
) : AbstractLincheckTest() {
    private val s = semaphore

    @Operation(allowExtraSuspension = true, promptCancellation = false)
    suspend fun acquire() = s.acquire()

    @Operation(handleExceptionsAsResult = [IllegalStateException::class])
    fun release() = s.release()

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        actorsBefore(0)
        .sequentialSpecification(seqSpec.java)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}

class AsyncSemaphore1LincheckTest : AsyncSemaphoreLincheckTestBase(AsyncSemaphore(1), SemaphoreUnboundedSequential1::class)
class AsyncSemaphore2LincheckTest : AsyncSemaphoreLincheckTestBase(AsyncSemaphore(2), SemaphoreUnboundedSequential2::class)

class AsyncSemaphoreSmart1LincheckTest : AsyncSemaphoreLincheckTestBase(AsyncSemaphoreSmart(1), SemaphoreUnboundedSequential1::class)
class AsyncSemaphoreSmart2LincheckTest : AsyncSemaphoreLincheckTestBase(AsyncSemaphoreSmart(2), SemaphoreUnboundedSequential2::class)

class SyncSemaphoreSmart1LincheckTest : SemaphoreLincheckTestBase(SyncSemaphoreSmart(1), SemaphoreUnboundedSequential1::class) {
    override fun ModelCheckingOptions.customize(isStressTest: Boolean) = checkObstructionFreedom(false)
}
class SyncSemaphoreSmart2LincheckTest : SemaphoreLincheckTestBase(SyncSemaphoreSmart(2), SemaphoreUnboundedSequential2::class) {
    override fun ModelCheckingOptions.customize(isStressTest: Boolean) = checkObstructionFreedom(false)
}


// ####################################
// # COUNT-DOWN-LATCH SYNCHRONIZATION #
// ####################################

/**
 * This primitive allows to wait until several operation are completed.
 * It is initialized with a given count, and each [countDown] invocation
 * decrements the count of remaining operations to be completed. At the
 * same time, [await] suspends until this count reaches zero.
 *
 * This implementation uses simple cancellation, so the [countDown] invocation
 * that reaches the counter zero works in a linear of the number of [await]
 * invocations, including the ones that are already cancelled.
 */
internal open class CountDownLatch(count: Int) : SegmentQueueSynchronizer<Unit>() {
    override val resumeMode get() = ASYNC

    private val count = atomic(count)
    // The number of suspended `await` invocations.
    // `DONE_MARK` should be set when the count reaches zero,
    // so the following suspension attempts detect this change by
    // checking the mark and complete immediately in this case.
    private val waiters = atomic(0)

    protected fun decWaiters() = waiters.decrementAndGet()

    /**
     * Decrements the count and resumes waiting
     * [await] invocations if it reaches zero.
     */
    fun countDown() {
        // Decrement the count.
        val r = count.decrementAndGet()
        // Should the waiters be resumed?
        if (r <= 0) resumeWaiters()
    }

    private fun resumeWaiters() {
        val w = waiters.getAndUpdate { cur ->
            // Is the done mark set?
            if (cur and DONE_MARK != 0) return
            cur or DONE_MARK
        }
        // This thread has successfully set
        // the mark, resume the waiters.
        repeat(w) { resume(Unit) }
    }

    /**
     * Waits until the count reaches zero,
     * completes immediately if it is already zero.
     */
    suspend fun await() {
        // Check whether the count has already reached zero;
        // this check can be considered as an optimization.
        if (remaining() == 0) return
        // Increment the number of waiters and check
        // that `DONE_MARK` is not set, finish otherwise.
        val w = waiters.incrementAndGet()
        if (w and DONE_MARK != 0) return
        // The number of waiters is
        // successfully incremented, suspend.
        suspendCancellableCoroutine<Unit> { suspend(it) }
    }

    /**
     * Returns the current count.
     */
    fun remaining(): Int = count.value.coerceAtLeast(0)

    protected companion object {
        const val DONE_MARK = 1 shl 31
    }
}

/**
 * This implementation uses the smart cancellation mode, so the [countDown]
 * invocation that reaches the counter zero works in linear of the number
 * of non-cancelled [await] invocations. This way, it does not matter
 * how many [await] requests has been cancelled - they do not play any role.
 */
internal class CountDownLatchSmart(count: Int) : CountDownLatch(count) {
    override val resumeMode: ResumeMode get() = ASYNC
    override val cancellationMode get() = SMART

    override fun onCancellation(): Boolean {
        // Decrement the number of waiters.
        val w = decWaiters()
        // Succeed if the `DONE_MARK` is not set yet.
        return (w and DONE_MARK) == 0
    }
}

internal abstract class CountDownLatchLincheckTestBase(
    private val cdl: CountDownLatch,
    private val seqSpec: KClass<*>
) : AbstractLincheckTest() {
    @Operation
    fun countDown() = cdl.countDown()

    @Operation
    fun remaining() = cdl.remaining()

    @Operation(promptCancellation = false)
    suspend fun await() = cdl.await()

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        actorsBefore(0)
        .actorsAfter(0)
        .sequentialSpecification(seqSpec.java)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}

class CountDownLatchSequential1 : CountDownLatchSequential(1)
class CountDownLatchSequential2 : CountDownLatchSequential(2)

internal class CountDownLatch1LincheckTest : CountDownLatchLincheckTestBase(CountDownLatch(1), CountDownLatchSequential1::class)
internal class CountDownLatch2LincheckTest : CountDownLatchLincheckTestBase(CountDownLatch(2), CountDownLatchSequential2::class)

internal class CountDownLatchSmart1LincheckTest : CountDownLatchLincheckTestBase(CountDownLatchSmart(1), CountDownLatchSequential1::class)
internal class CountDownLatchSmart2LincheckTest : CountDownLatchLincheckTestBase(CountDownLatchSmart(2), CountDownLatchSequential2::class)

open class CountDownLatchSequential(initialCount: Int) : VerifierState() {
    private var count = initialCount
    private val waiters = ArrayList<CancellableContinuation<Unit>>()

    fun countDown() {
        if (--count == 0) {
            waiters.forEach { it.tryResume0(Unit, {}) }
            waiters.clear()
        }
    }

    suspend fun await() {
        if (count <= 0) return
        suspendCancellableCoroutine<Unit> { cont ->
            waiters.add(cont)
        }
    }

    fun remaining(): Int = count.coerceAtLeast(0)

    override fun extractState() = remaining()
}


// ###########################
// # BARRIER SYNCHRONIZATION #
// ###########################

/**
 * This synchronization primitive allows a set of coroutines to
 * all wait for each other to reach a common barrier point.
 *
 * The implementation is straightforward: it maintains a counter
 * of arrived coroutines and increments it in the beginning of
 * [arrive] operation. The last coroutine should resume all the
 * previously arrived ones.
 *
 * In case of cancellation, the handler decrements the counter if
 * not all the parties are arrived. However, it is impossible to
 * make cancellation atomic (e.g., Java's implementation simply
 * does not work in case of thread interruption) since there is
 * no way to resume a set of coroutines atomically. However,
 * this implementation is correct with prompt cancellation.
 */
internal class Barrier(private val parties: Int) : SegmentQueueSynchronizer<Unit>() {
    override val resumeMode get() = ASYNC
    override val cancellationMode get() = SMART

    // The number of coroutines arrived to this barrier point.
    private val arrived = atomic(0L)

    /**
     * Waits for other parties and returns `true`.
     * Fails if this invocation exceeds the number
     * of parties, returns `false` in this case.
     *
     * It is also possible to make this barrier
     * implementation cyclic after introducing
     * `resume(count, value)` operation on the
     * `SegmentQueueSynchronizer`, which resumes
     * the specified number of coroutines and
     * with the same value atomically.
     */
    suspend fun arrive(): Boolean {
        // Are all parties has already arrived?
        if (arrived.value > parties)
            return false // fail this `arrive()`.
        // Increment the number of arrived parties.
        val a = arrived.incrementAndGet()
        return when {
            // Should we suspend?
            a < parties -> {
                suspendCoroutine<Unit> { cont -> suspend(cont) }
                true
            }
            // Are we the last party?
            a == parties.toLong() -> {
                // Resume all waiters.
                repeat(parties - 1) {
                    resume(Unit)
                }
                true
            }
            // Should we fail?
            else -> false
        }
    }

    override fun onCancellation(): Boolean {
        // Decrement the number of arrived parties if possible.
        arrived.loop { cur ->
            // Are we going to be resumed?
            // The resumption permit should be refused in this case.
            if (cur == parties.toLong()) return false
            // Successful cancellation, return `true`.
            if (arrived.compareAndSet(cur, cur - 1)) return true
        }
    }
}

abstract class BarrierLincheckTestBase(parties: Int, val seqSpec: KClass<*>) : AbstractLincheckTest() {
    private val b = Barrier(parties)

    @Operation(promptCancellation = false)
    suspend fun arrive() = b.arrive()

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean) =
        actorsBefore(0)
        .actorsAfter(0)
        .threads(3)
        .sequentialSpecification(seqSpec.java)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}

class BarrierSequential1 : BarrierSequential(1)
class Barrier1LincheckTest : BarrierLincheckTestBase(1, BarrierSequential1::class)
class BarrierSequential2 : BarrierSequential(2)
class Barrier2LincheckTest : BarrierLincheckTestBase(2, BarrierSequential2::class)
class BarrierSequential3 : BarrierSequential(3)
class Barrier3LincheckTest : BarrierLincheckTestBase(3, BarrierSequential3::class)

open class BarrierSequential(parties: Int) : VerifierState() {
    private var remaining = parties
    private val waiters = ArrayList<Continuation<Unit>>()

    suspend fun arrive(): Boolean {
        val r = --remaining
        return when {
            r > 0 -> {
                suspendCancellableCoroutine<Unit> { cont ->
                    waiters.add(cont)
                    cont.invokeOnCancellation {
                        remaining++
                        waiters.remove(cont)
                    }
                }
                true
            }
            r == 0 -> {
                waiters.forEach { it.resume(Unit) }
                true
            }
            else -> false
        }
    }

    override fun extractState() = remaining > 0
}


// ##################
// # BLOCKING POOLS #
// ##################

/**
 * While using resources such as database connections, sockets, etc.,
 * it is common to reuse them; that requires a fast and handy mechanism.
 * This [BlockingPool] abstraction maintains a set of elements that can be put
 * into the pool for further reuse or be retrieved to process the current operation.
 * When [retrieve] comes to an empty pool, it blocks, and the following [put] operation
 * resumes it; all the waiting requests are processed in the first-in-first-out (FIFO) order.
 *
 * In our tests we consider two pool implementations: the [queue-based][BlockingQueuePool]
 * and the [stack-based][BlockingStackPool]. Intuitively, the queue-based implementation is
 * faster since it is built on arrays and uses `Fetch-And-Add`-s on the contended path,
 * while the stack-based pool retrieves the last inserted, thus, the "hottest", element.
 *
 * Please note that both these implementations are not linearizable and can retrieve elements
 * out-of-order under some races. However, since pools by themselves do not guarantee
 * that the stored elements are ordered (the one may consider them as bags),
 * these queue- and stack-based versions should be considered as pools with specific heuristics.
 */
interface BlockingPool<T: Any> {
    /**
     * Either resumes the first waiting [retrieve] operation
     * and passes the [element] to it, or simply puts the
     * [element] into the pool.
     */
    fun put(element: T)

    /**
     * Retrieves one of the elements from the pool
     * (the order is not specified), or suspends if it is
     * empty -- the following [put] operations resume
     * waiting [retrieve]-s in the first-in-first-out order.
     */
    suspend fun retrieve(): T
}

/**
 * This pool uses queue under the hood and is implemented with simple cancellation.
 */
internal class BlockingQueuePool<T: Any> : SegmentQueueSynchronizer<T>(), BlockingPool<T> {
    override val resumeMode get() = ASYNC

    // > 0 -- number of elements;
    // = 0 -- empty pool;
    // < 0 -- number of waiters.
    private val availableElements = atomic(0L)

    // This is an infinite array by design, a plain array is used for simplicity.
    private val elements = atomicArrayOfNulls<Any?>(100)

    // Indices in `elements` for the next `tryInsert()` and `tryRetrieve()` operations.
    // Each `tryInsert()`/`tryRetrieve()` pair works on a separate slot. When `tryRetrieve()`
    // comes earlier, it marks the slot as `BROKEN` so both this operation and the
    // corresponding `tryInsert()` fail.
    private val insertIdx = atomic(0)
    private val retrieveIdx = atomic(0)

    override fun put(element: T) {
        while (true) {
            // Increment the number of elements in advance.
            val b = availableElements.getAndIncrement()
            // Is there a waiting `retrieve`?
            if (b < 0) {
                // Try to resume the first waiter,
                // can fail if it is already cancelled.
                if (resume(element)) return
            } else {
                // Try to insert the element into the
                // queue, can fail if the slot is broken.
                if (tryInsert(element)) return
            }
        }
    }

    /**
     * Tries to insert the [element] into the next
     * [elements] array slot. Returns `true` if
     * succeeds, or `false` if the slot is [broken][BROKEN].
     */
    private fun tryInsert(element: T): Boolean {
        val i = insertIdx.getAndIncrement()
        return elements[i].compareAndSet(null, element)
    }

    override suspend fun retrieve(): T {
        while (true) {
            // Decrements the number of elements.
            val b = availableElements.getAndDecrement()
            // Is there an element in the pool?
            if (b > 0) {
                // Try to retrieve the first element,
                // can fail if the first slot
                // is empty due to a race.
                val x = tryRetrieve()
                if (x != null) return x
            } else {
                // The pool is empty, suspend.
                return suspendCancellableCoroutine { cont ->
                    suspend(cont)
                }
            }
        }
    }

    /**
     * Tries to retrieve the first element from
     * the [elements] array. Returns the element if
     * succeeds, or `null` if the first slot is empty
     * due to a race -- it marks the slot as [broken][BROKEN]
     * in this case, so the corresponding [tryInsert]
     * invocation fails.
     */
    @Suppress("UNCHECKED_CAST")
    private fun tryRetrieve(): T? {
        val i = retrieveIdx.getAndIncrement()
        return elements[i].getAndSet(BROKEN) as T?
    }

    fun stateRepresentation(): String {
        val elementsBetweenIndices = mutableListOf<Any?>()
        val first = kotlin.math.min(retrieveIdx.value, insertIdx.value)
        val last = kotlin.math.max(retrieveIdx.value, insertIdx.value)
        for (i in first until last) {
            elementsBetweenIndices.add(elements[i].value)
        }
        return "availableElements=${availableElements.value}," +
            "insertIdx=${insertIdx.value}," +
            "retrieveIdx=${retrieveIdx.value}," +
            "elements=$elementsBetweenIndices," +
            "sqs=<${super.toString()}>"
    }

    companion object {
        @JvmStatic
        val BROKEN = Symbol("BROKEN")
    }
}

/**
 * This pool uses stack under the hood and shows how to use
 * smart cancellation for data structures that store resources.
 */
internal class BlockingStackPool<T: Any> : SegmentQueueSynchronizer<T>(), BlockingPool<T> {
    override val resumeMode get() = ASYNC
    override val cancellationMode get() = SMART

    // The stack is implemented via a concurrent linked list,
    // this is its head; `null` means that the stack is empty.
    private val head = atomic<StackNode<T>?>(null)

    // > 0 -- number of elements;
    // = 0 -- empty pool;
    // < 0 -- number of waiters.
    private val availableElements = atomic(0)

    override fun put(element: T) {
        while (true) {
            // Increment the number of elements in advance.
            val b = availableElements.getAndIncrement()
            // Is there a waiting retrieve?
            if (b < 0) {
                // Resume the first waiter, never fails
                // in the smart cancellation mode.
                resume(element)
                return
            } else {
                // Try to insert the element into the
                // stack, can fail if a concurrent [tryRetrieve]
                // came earlier and marked it with a failure node.
                if (tryInsert(element)) return
            }
        }
    }

    /**
     * Tries to insert the [element] into the stack.
     * Returns `true` on success`, or `false` if the
     * stack is marked with a failure node, retrieving
     * it in this case.
     */
    private fun tryInsert(element: T): Boolean = head.loop { h ->
        // Is the stack marked with a failure node?
        if (h != null && h.element == null) {
            // Try to retrieve the failure node.
            if (head.compareAndSet(h, h.next)) return false
        } else {
            // Try to insert the element.
            val newHead = StackNode(element, h)
            if (head.compareAndSet(h, newHead)) return true
        }
    }

    override suspend fun retrieve(): T {
        while (true) {
            // Decrement the number of elements.
            val b = availableElements.getAndDecrement()
            // Is there an element in the pool?
            if (b > 0) {
                // Try to retrieve the top element,
                // can fail if the stack if empty
                // due to a race.
                val x = tryRetrieve()
                if (x != null) return x
            } else {
                // The pool is empty, suspend.
                return suspendCancellableCoroutine { cont ->
                    suspend(cont)
                }
            }
        }
    }

    /**
     * Tries to retrieve the top (last) element and return `true`
     * if the stack is not empty; returns `false` and
     * inserts a failure node otherwise.
     */
    @Suppress("NullChecksToSafeCall")
    private fun tryRetrieve(): T? = head.loop { h ->
        // Is the queue empty or full of failure nodes?
        if (h == null || h.element == null) {
            // Try to add one more failure node and fail.
            val failNode = StackNode(null, h)
            if (head.compareAndSet(h, failNode)) return null
        } else {
            // Try to retrieve the top element.
            if (head.compareAndSet(h, h.next)) return h.element
        }
    }

    // The logic of cancellation is very similar to the one
    // in semaphore, with the only difference that elements
    // should be physically returned to the pool.
    override fun onCancellation(): Boolean {
        val b = availableElements.getAndIncrement()
        return b < 0
    }

    // If an element is refused, it should be inserted back to the stack.
    override fun tryReturnRefusedValue(value: T) = tryInsert(value)

    // In order to return the value back
    // to the pool, [put] is naturally used.
    override fun returnValue(value: T) = put(value)

    internal fun stateRepresentation(): String {
        val elements = ArrayList<T?>()
        var curNode = head.value
        while (curNode != null) {
            elements += curNode.element
            curNode = curNode.next
        }
        return "availableElements=${availableElements.value},elements=$elements,sqs=<${super.toString()}>"
    }

    class StackNode<T>(val element: T?, val next: StackNode<T>?)
}

abstract class BlockingPoolLincheckTestBase(val p: BlockingPool<Unit>) : AbstractLincheckTest() {
    @Operation
    fun put() = p.put(Unit)

    @Suppress("NullChecksToSafeCall")
    @Operation(allowExtraSuspension = true, promptCancellation = false)
    suspend fun retrieve() = p.retrieve()

    @StateRepresentation
    fun stateRepresentation() = when(p) {
        is BlockingStackPool<*> -> p.stateRepresentation()
        is BlockingQueuePool<*> -> p.stateRepresentation()
        else -> error("Unknown pool type: ${p::class.simpleName}")
    }

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean) =
        sequentialSpecification(BlockingPoolUnitSequential::class.java)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}
class BlockingQueuePoolLincheckTest : BlockingPoolLincheckTestBase(BlockingQueuePool())
class BlockingStackPoolLincheckTest : BlockingPoolLincheckTestBase(BlockingStackPool())

class BlockingPoolUnitSequential : VerifierState() {
    private var elements = 0
    private val waiters = ArrayList<CancellableContinuation<Unit>>()

    fun put() {
        while (true) {
            if (waiters.isNotEmpty()) {
                val w = waiters.removeAt(0)
                if (w.tryResume0(Unit, { put() })) return
            } else {
                elements ++
                return
            }
        }
    }

    suspend fun retrieve() {
        if (elements > 0) {
            elements--
        } else {
            suspendCancellableCoroutine<Unit> { cont ->
                waiters.add(cont)
            }
        }
    }

    override fun extractState() = elements
}


// ##################
// # BLOCKING QUEUE #
// ##################

/**
 * This algorithm maintains a separate queue for elements so blocked [receive] operations
 * retrieve elements _after_ resumption from this queue. Similar to other data structures,
 * an atomic [size] counter is maintained to decide whether the queue is empty for [receive]
 * and whether there is a waiting receiver for [send].
 *
 * Comparing to the blocking pools above, this implementation is fully linearizable but requires
 * the waiters to retrieve elements from separate storage after the resumption. However, we find
 * this implementation more flexible since any container (not only the FIFO queue) can be used
 * under the hood. It is also safe in case of prompt cancellation since the elements cannot be lost.
 */
internal class BlockingQueueSmart<E : Any> : SegmentQueueSynchronizer<Unit>() {
    private val size = atomic(0) // #send - #receive
    private val elements = ConcurrentLinkedQueue<E>() // any queue can be here, even not FIFO.

    override val resumeMode get() = ASYNC
    override val cancellationMode get() = SMART

    /**
     * Puts the specified [element] into the queue
     * or transfers it to the first waiting receiver.
     */
    fun send(element: E) {
        elements.add(element) // store the element into queue at first.
        val s = size.getAndIncrement() // increment the number of elements.
        if (s < 0) { // is there a waiting receiver?
            resume(Unit) // resume the first waiter.
        }
    }

    suspend fun receive(): E {
        val s = size.getAndDecrement() // decrement the number of available elements.
        if (s <= 0) { // should this `receive()` suspend?
            suspendCancellableCoroutine<Unit> { suspend(it) }
        }
        return elements.remove() // retrieve the first element.
    }

    override fun onCancellation(): Boolean {
        val s = size.getAndIncrement() // decrement the number of waiting `receive()`-s.
        return s < 0 // succeed if this `receive()` is not already resumed.
    }

    // For prompt cancellation; no need to return elements since
    // they are not transferred via SQS but stored separately.
    override fun returnValue(value: Unit) {
        val b = size.getAndIncrement()
        if (b < 0) resume(Unit)
    }
}

class BlockingQueueSmartLincheckTest : AbstractLincheckTest() {
    private val c = BlockingQueueSmart<Int>()

    @Operation
    fun send(element: Int) = c.send(element)

    @Operation(allowExtraSuspension=true, promptCancellation = false)
    suspend fun receive() = c.receive()

    override fun <O : Options<O, *>> O.customize(isStressTest: Boolean): O =
        logLevel(LoggingLevel.INFO)
        .sequentialSpecification(BlockingQueueSequential::class.java)

    override fun ModelCheckingOptions.customize(isStressTest: Boolean) =
        checkObstructionFreedom()
}

class BlockingQueueSequential : VerifierState() {
    private val receivers = ArrayList<CancellableContinuation<Unit>>()
    private val elements = ArrayList<Int>()

    fun send(element: Int) {
        if (receivers.isNotEmpty()) {
            val r = receivers.removeAt(0)
            elements += element
            r.resume(Unit)
        } else {
            elements += element
        }
    }

    suspend fun receive(): Int =
        if (elements.isNotEmpty()) {
            retrieveFirstElement()
        } else {
            suspendCancellableCoroutine<Unit> { cont ->
                receivers += cont
                cont.invokeOnCancellation { receivers.remove(cont) }
            }
            retrieveFirstElement()
        }

    private fun retrieveFirstElement(): Int {
        return elements.removeAt(0)
    }

    override fun extractState() = elements
}