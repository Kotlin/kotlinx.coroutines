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

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.internal.LockFreeLinkedListHead
import kotlinx.coroutines.experimental.internal.LockFreeLinkedListNode
import java.util.concurrent.atomic.AtomicReferenceFieldUpdater

/**
 * Mutual exclusion for coroutines.
 *
 * Mutex has two states: _locked_ and _unlocked_.
 * It is **non-reentrant**, that is invoking [lock] even from the same thread/coroutine that currently holds
 * the lock still suspends the invoker.
 *
 * @param locked initial state of the mutex
 */
public class Mutex(locked: Boolean = false) {
    // State is: Empty | UnlockOp | LockFreeLinkedListHead (queue of Waiter objects)
    @Volatile
    private var state: Any? = if (locked) EmptyLocked else EmptyUnlocked // shared objects while we have no waiters

    private companion object {
        @JvmStatic
        val STATE: AtomicReferenceFieldUpdater<Mutex, Any?> =
            AtomicReferenceFieldUpdater.newUpdater(Mutex::class.java, Any::class.java, "state")

        @JvmStatic
        val EmptyLocked = Empty(true)

        @JvmStatic
        val EmptyUnlocked = Empty(false)

        @JvmStatic
        fun isLocked(state: Any?) = state !is Empty || state.locked

    }

    /**
     * Returns `true` when this mutex is locked.
     */
    public val isLocked: Boolean get() = isLocked(state)

    /**
     * Tries to lock this mutex, returning `false` if this mutex is already locked.
     */
    public fun tryLock(): Boolean {
        while (true) { // lock-free loop on state
            val state = this.state
            when (state) {
                is Empty -> {
                    if (state.locked) return false
                    if (STATE.compareAndSet(this, state, EmptyLocked)) return true
                }
                is UnlockOp -> state.helpComplete() // help
                else -> return false
            }
        }
    }

    /**
     * Locks this mutex, suspending caller while the mutex is locked.
     *
     * This suspending function is cancellable. If the [Job] of the current coroutine is completed while this
     * function is suspended, this function immediately resumes with [CancellationException].
     * Cancellation of suspended lock invocation is *atomic* -- when this function
     * throws [CancellationException] it means that the mutex was not locked.
     *
     * Note, that this function does not check for cancellation when it is not suspended.
     * Use [yield] or [CoroutineScope.isActive] to periodically check for cancellation in tight loops if needed.
     */
    public suspend fun lock() {
        // fast-path -- try lock
        if (tryLock()) return
        // slow-path -- suspend
        return lockSuspend()
    }

    private suspend fun lockSuspend() = suspendCancellableCoroutine<Unit>(holdCancellability = true) sc@ { cont ->
        val waiter = Waiter(cont)
        loop@ while (true) { // lock-free loop on state
            val state = this.state
            when (state) {
                is Empty -> {
                    if (state.locked) {
                        // try upgrade to queue & retry
                        STATE.compareAndSet(this, state, LockFreeLinkedListHead())
                        continue@loop
                    } else {
                        // try lock
                        if (STATE.compareAndSet(this, state, EmptyLocked)) {
                            // locked
                            cont.resume(Unit)
                            return@sc
                        }
                    }
                }
                is UnlockOp -> { // help & retry
                    state.helpComplete()
                    continue@loop
                }
                else -> {
                    state as LockFreeLinkedListHead // type assertion
                    if (state.addLastIf(waiter, { this.state === state })) {
                        // added to waiter list!
                        cont.initCancellability()
                        cont.removeOnCompletion(waiter)
                        return@sc
                    }
                }
            }
        }
    }

    /**
     * Unlocks this mutex. Throws [IllegalStateException] if invoked on a mutex that is not locked.
     */
    public fun unlock() {
        while (true) { // lock-free loop on state
            val state = this.state
            when (state) {
                is Empty -> {
                    check(state.locked) { "Mutex is not locked" }
                    if (STATE.compareAndSet(this, state, EmptyUnlocked)) return
                }
                is UnlockOp -> state.helpComplete()
                else -> {
                    state as LockFreeLinkedListHead // type assertion
                    val waiter = state.removeFirstOrNull()
                    if (waiter == null) {
                        val op = UnlockOp(state)
                        if (STATE.compareAndSet(this, state, op) && op.helpComplete()) return
                    } else {
                        val cont = (waiter as Waiter).cont
                        val token = cont.tryResume(Unit)
                        if (token != null) {
                            // successfully resumed waiter that now is holding the lock
                            cont.completeResume(token)
                            return
                        }
                    }
                }
            }
        }
    }

    private class Empty(val locked: Boolean) {
        override fun toString(): String = "Empty[${if (locked) "Locked" else "Unlocked"}]";
    }

    private class Waiter(val cont: CancellableContinuation<Unit>) : LockFreeLinkedListNode()

    // atomic unlock operation that checks that waiters queue is empty
    private inner class UnlockOp(val queue: LockFreeLinkedListHead) {
        fun helpComplete(): Boolean {
            /*
               Note: queue cannot change while this UnlockOp is in progress, so all concurrent attempts to
               make a decision will reach it consistently. It does not matter what is a proposed
               decision when this UnlockOp is not longer active, because in this case the following CAS
               will fail anyway.
             */
            val success = queue.isEmpty
            val update: Any = if (success) EmptyUnlocked else queue
            STATE.compareAndSet(this@Mutex, this@UnlockOp, update)
            /*
                `helpComplete` invocation from the original `unlock` invocation may be coming too late, when
                some other thread had already helped to complete it (either successfully or not).
                That operation was unsuccessful if `state` was restored to this `queue` reference and
                that is what is being checked below.
             */
            return state !== queue
        }
    }
}