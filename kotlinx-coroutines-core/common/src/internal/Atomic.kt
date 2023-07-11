/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.internal

import kotlinx.atomicfu.atomic
import kotlinx.coroutines.*
import kotlin.jvm.*

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

    /**
     * Returns reference to atomic operation that this descriptor is a part of or `null`
     * if not a part of any [AtomicOp].
     */
    abstract val atomicOp: AtomicOp<*>?

    override fun toString(): String = "$classSimpleName@$hexAddress" // debug
}

@JvmField
internal val NO_DECISION: Any = Symbol("NO_DECISION")

/**
 * Descriptor for multi-word atomic operation.
 * Based on paper
 * ["A Practical Multi-Word Compare-and-Swap Operation"](https://www.cl.cam.ac.uk/research/srg/netos/papers/2002-casn.pdf)
 * by Timothy L. Harris, Keir Fraser and Ian A. Pratt.
 *
 * Note: parts of atomic operation must be globally ordered. Otherwise, this implementation will produce
 * `StackOverflowError`.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@InternalCoroutinesApi
public abstract class AtomicOp<in T> : OpDescriptor() {
    private val _consensus = atomic<Any?>(NO_DECISION)

    override val atomicOp: AtomicOp<*> get() = this

    private fun decide(decision: Any?): Any? {
        assert { decision !== NO_DECISION }
        val current = _consensus.value
        if (current !== NO_DECISION) return current
        if (_consensus.compareAndSet(NO_DECISION, decision)) return decision
        return _consensus.value
    }

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
        // complete operation
        complete(affected as T, decision)
        return decision
    }
}
