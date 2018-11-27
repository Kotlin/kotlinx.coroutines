/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.atomicfu.atomic

/**
 * The most abstract operation that can be in process. Other threads observing an instance of this
 * class in the fields of their object shall invoke [perform] to help.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public abstract class OpDescriptor {
    /**
     * Returns `null` is operation was performed successfully or some other
     * object that indicates the failure reason.
     */
    abstract fun perform(affected: Any?): Any?
}

@SharedImmutable
private val NO_DECISION: Any = Symbol("NO_DECISION")

/**
 * Descriptor for multi-word atomic operation.
 * Based on paper
 * ["A Practical Multi-Word Compare-and-Swap Operation"](http://www.cl.cam.ac.uk/research/srgnetos/papers/2002-casn.pdf)
 * by Timothy L. Harris, Keir Fraser and Ian A. Pratt.
 *
 * Note: parts of atomic operation must be globally ordered. Otherwise, this implementation will produce
 * `StackOverflowError`.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public abstract class AtomicOp<in T> : OpDescriptor() {
    private val _consensus = atomic<Any?>(NO_DECISION)

    val isDecided: Boolean get() = _consensus.value !== NO_DECISION

    fun tryDecide(decision: Any?): Boolean {
        check(decision !== NO_DECISION)
        return _consensus.compareAndSet(NO_DECISION, decision)
    }

    private fun decide(decision: Any?): Any? = if (tryDecide(decision)) decision else _consensus.value

    abstract fun prepare(affected: T): Any? // `null` if Ok, or failure reason

    abstract fun complete(affected: T, failure: Any?) // failure != null if failed to prepare op

    // returns `null` on success
    @Suppress("UNCHECKED_CAST")
    final override fun perform(affected: Any?): Any? {
        // make decision on status
        var decision = this._consensus.value
        if (decision === NO_DECISION) {
            decision = decide(prepare(affected as T))
        }

        complete(affected as T, decision)
        return decision
    }
}

/**
 * A part of multi-step atomic operation [AtomicOp].
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public abstract class AtomicDesc {
    abstract fun prepare(op: AtomicOp<*>): Any? // returns `null` if prepared successfully
    abstract fun complete(op: AtomicOp<*>, failure: Any?) // decision == null if success
}
