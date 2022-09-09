/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.sync

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlinx.coroutines.selects.*
import kotlin.contracts.*
import kotlin.jvm.*

/**
 * Mutual exclusion for coroutines.
 *
 * Mutex has two states: _locked_ and _unlocked_.
 * It is **non-reentrant**, that is invoking [lock] even from the same thread/coroutine that currently holds
 * the lock still suspends the invoker.
 *
 * JVM API note:
 * Memory semantic of the [Mutex] is similar to `synchronized` block on JVM:
 * An unlock operation on a [Mutex] happens-before every subsequent successful lock on that [Mutex].
 * Unsuccessful call to [tryLock] do not have any memory effects.
 */
public interface Mutex {
    /**
     * Returns `true` if this mutex is locked.
     */
    public val isLocked: Boolean

    /**
     * Tries to lock this mutex, returning `false` if this mutex is already locked.
     *
     * It is recommended to use [withLock] for safety reasons, so that the acquired lock is always
     * released at the end of your critical section, and [unlock] is never invoked before a successful
     * lock acquisition.
     *
     * @param owner Optional owner token for debugging. When `owner` is specified (non-null value) and this mutex
     *        is already locked with the same token (same identity), this function throws [IllegalStateException].
     */
    public fun tryLock(owner: Any? = null): Boolean

    /**
     * Locks this mutex, suspending caller while the mutex is locked.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is cancelled or completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     * There is a **prompt cancellation guarantee**. If the job was cancelled while this function was
     * suspended, it will not resume successfully. See [suspendCancellableCoroutine] documentation for low-level details.
     * This function releases the lock if it was already acquired by this function before the [CancellationException]
     * was thrown.
     *
     * Note that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     *
     * Use [tryLock] to try acquiring the lock without waiting.
     *
     * This function is fair; suspended callers are resumed in first-in-first-out order.
     *
     * It is recommended to use [withLock] for safety reasons, so that the acquired lock is always
     * released at the end of the critical section, and [unlock] is never invoked before a successful
     * lock acquisition.
     *
     * @param owner Optional owner token for debugging. When `owner` is specified (non-null value) and this mutex
     *        is already locked with the same token (same identity), this function throws [IllegalStateException].
     */
    public suspend fun lock(owner: Any? = null)

    /**
     * Clause for [select] expression of [lock] suspending function that selects when the mutex is locked.
     * Additional parameter for the clause in the `owner` (see [lock]) and when the clause is selected
     * the reference to this mutex is passed into the corresponding block.
     */
    @Deprecated(level = DeprecationLevel.WARNING, message = "Mutex.onLock deprecated without replacement. " +
        "For additional details please refer to #2794") // WARNING since 1.6.0
    public val onLock: SelectClause2<Any?, Mutex>

    /**
     * Checks whether this mutex is locked by the specified owner.
     *
     * @return `true` when this mutex is locked by the specified owner;
     * `false` if the mutex is not locked or locked by another owner.
     */
    public fun holdsLock(owner: Any): Boolean

    /**
     * Unlocks this mutex. Throws [IllegalStateException] if invoked on a mutex that is not locked or
     * was locked with a different owner token (by identity).
     *
     * It is recommended to use [withLock] for safety reasons, so that the acquired lock is always
     * released at the end of the critical section, and [unlock] is never invoked before a successful
     * lock acquisition.
     *
     * @param owner Optional owner token for debugging. When `owner` is specified (non-null value) and this mutex
     *        was locked with the different token (by identity), this function throws [IllegalStateException].
     */
    public fun unlock(owner: Any? = null)
}

/**
 * Creates a [Mutex] instance.
 * The mutex created is fair: lock is granted in first come, first served order.
 *
 * @param locked initial state of the mutex.
 */
@Suppress("FunctionName")
public fun Mutex(locked: Boolean = false): Mutex =
    MutexImpl(locked)

/**
 * Executes the given [action] under this mutex's lock.
 *
 * @param owner Optional owner token for debugging. When `owner` is specified (non-null value) and this mutex
 *        is already locked with the same token (same identity), this function throws [IllegalStateException].
 *
 * @return the return value of the action.
 */
@OptIn(ExperimentalContracts::class)
public suspend inline fun <T> Mutex.withLock(owner: Any? = null, action: () -> T): T {
    contract {
        callsInPlace(action, InvocationKind.EXACTLY_ONCE)
    }

    lock(owner)
    try {
        return action()
    } finally {
        unlock(owner)
    }
}


internal open class MutexImpl(locked: Boolean) : SemaphoreImpl(1, if (locked) 1 else 0), Mutex {
    /**
     * After the lock is acquired, the corresponding owner is stored in this field.
     * The [unlock] operation checks the owner and either re-sets it to [NO_OWNER],
     * if there is no waiting request, or to the owner of the suspended [lock] operation
     * to be resumed, otherwise.
     */
    private val owner = atomic<Any?>(if (locked) null else NO_OWNER)

    private val onSelectCancellationUnlockConstructor: OnCancellationConstructor =
        { _: SelectInstance<*>, owner: Any?, _: Any? ->
            { unlock(owner) }
        }

    override val isLocked: Boolean get() =
        availablePermits == 0

    override fun holdsLock(owner: Any): Boolean {
        while (true) {
            // Is this mutex locked?
            if (!isLocked) return false
            val curOwner = this.owner.value
            // Wait in a spin-loop until the owner is set
            if (curOwner === NO_OWNER) continue // <-- ATTENTION, BLOCKING PART HERE
            // Check the owner
            return curOwner === owner
        }
    }

    override suspend fun lock(owner: Any?) {
        if (tryLock(owner)) return
        lockSuspend(owner)
    }

    private suspend fun lockSuspend(owner: Any?) = suspendCancellableCoroutineReusable { cont ->
        val contWithOwner = CancellableContinuationWithOwner(cont, owner)
        acquire(contWithOwner)
    }

    override fun tryLock(owner: Any?): Boolean =
        if (tryAcquire()) {
            assert { this.owner.value === NO_OWNER }
            this.owner.value = owner
            true
        } else {
            false
        }

    override fun unlock(owner: Any?) {
        while (true) {
            // Is this mutex locked?
            check(isLocked) { "This mutex is not locked" }
            // Read the owner, waiting until it is set in a spin-loop if required.
            val curOwner = this.owner.value
            if (curOwner === NO_OWNER) continue // <-- ATTENTION, BLOCKING PART HERE
            // Check the owner.
            check(curOwner === owner || owner == null) { "This mutex is locked by $curOwner, but $owner is expected" }
            // Try to clean the owner first. We need to use CAS here to synchronize with concurrent `unlock(..)`-s.
            if (!this.owner.compareAndSet(curOwner, NO_OWNER)) continue
            // Release the semaphore permit at the end.
            release()
            return
        }
    }

    @Suppress("UNCHECKED_CAST", "OverridingDeprecatedMember", "OVERRIDE_DEPRECATION")
    override val onLock: SelectClause2<Any?, Mutex> get() = SelectClause2Impl(
        clauseObject = this,
        regFunc = MutexImpl::onLockRegFunction as RegistrationFunction,
        processResFunc = MutexImpl::onLockProcessResult as ProcessResultFunction,
        onCancellationConstructor = onSelectCancellationUnlockConstructor
    )

    protected open fun onLockRegFunction(select: SelectInstance<*>, owner: Any?) {
        onAcquireRegFunction(SelectInstanceWithOwner(select, owner), owner)
    }

    protected open fun onLockProcessResult(owner: Any?, result: Any?): Any? {
        return this
    }

    private inner class CancellableContinuationWithOwner(
        @JvmField
        val cont: CancellableContinuation<Unit>,
        @JvmField
        val owner: Any?
    ) : CancellableContinuation<Unit> by cont {
        override fun tryResume(value: Unit, idempotent: Any?, onCancellation: ((cause: Throwable) -> Unit)?): Any? {
            assert { this@MutexImpl.owner.value === NO_OWNER }
            val token = cont.tryResume(value, idempotent) {
                assert { this@MutexImpl.owner.value.let { it === NO_OWNER ||it === owner } }
                this@MutexImpl.owner.value = owner
                unlock(owner)
            }
            if (token != null) {
                assert { this@MutexImpl.owner.value === NO_OWNER }
                this@MutexImpl.owner.value = owner
            }
            return token
        }

        override fun resume(value: Unit, onCancellation: ((cause: Throwable) -> Unit)?) {
            assert { this@MutexImpl.owner.value === NO_OWNER }
            this@MutexImpl.owner.value = owner
            cont.resume(value) { unlock(owner) }
        }
    }

    private inner class SelectInstanceWithOwner<Q>(
        @JvmField
        val select: SelectInstance<Q>,
        @JvmField
        val owner: Any?
    ) : SelectInstanceInternal<Q> by select as SelectInstanceInternal<Q> {
        override fun trySelect(clauseObject: Any, result: Any?): Boolean {
            assert { this@MutexImpl.owner.value === NO_OWNER }
            this@MutexImpl.owner.value = owner
            return select.trySelect(clauseObject, result).also { success ->
                if (!success) this@MutexImpl.owner.value = NO_OWNER
            }
        }

        override fun selectInRegistrationPhase(internalResult: Any?) {
            assert { this@MutexImpl.owner.value === NO_OWNER }
            this@MutexImpl.owner.value = owner
            select.selectInRegistrationPhase(internalResult)
        }
    }

    override fun toString() = "Mutex@${hexAddress}[isLocked=$isLocked,owner=${owner.value}]"
}

private val NO_OWNER = Symbol("NO_OWNER")
