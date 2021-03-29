/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
@file:Suppress("NO_EXPLICIT_VISIBILITY_IN_API_MODE")

package kotlinx.coroutines.internal

import kotlinx.atomicfu.atomic
import kotlinx.coroutines.*
import kotlin.jvm.*
import kotlin.native.concurrent.*

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

    fun isEarlierThan(that: OpDescriptor): Boolean {
        val thisOp = atomicOp ?: return false
        val thatOp = that.atomicOp ?: return false
        return thisOp.opSequence < thatOp.opSequence
    }
}

@SharedImmutable
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

    // Returns NO_DECISION when there is not decision yet
    val consensus: Any? get() = _consensus.value

    val isDecided: Boolean get() = _consensus.value !== NO_DECISION

    /**
     * Sequence number of this multi-word operation for deadlock resolution.
     * An operation with lower number aborts itself with (using [RETRY_ATOMIC] error symbol) if it encounters
     * the need to help the operation with higher sequence number and then restarts
     * (using higher `opSequence` to ensure progress).
     * Simple operations that cannot get into the deadlock always return zero here.
     *
     * See https://github.com/Kotlin/kotlinx.coroutines/issues/504
     */
    open val opSequence: Long get() = 0L

    override val atomicOp: AtomicOp<*> get() = this

    fun decide(decision: Any?): Any? {
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

/**
 * A part of multi-step atomic operation [AtomicOp].
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public abstract class AtomicDesc {
    lateinit var atomicOp: AtomicOp<*> // the reference to parent atomicOp, init when AtomicOp is created
    abstract fun prepare(op: AtomicOp<*>): Any? // returns `null` if prepared successfully
    abstract fun complete(op: AtomicOp<*>, failure: Any?) // decision == null if success
}

/**
 * It is returned as an error by [AtomicOp] implementations when they detect potential deadlock
 * using [AtomicOp.opSequence] numbers.
 */
@JvmField
@SharedImmutable
internal val RETRY_ATOMIC: Any = Symbol("RETRY_ATOMIC")
