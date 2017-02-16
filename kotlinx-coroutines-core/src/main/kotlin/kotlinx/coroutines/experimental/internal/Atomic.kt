package kotlinx.coroutines.experimental.internal

import java.util.concurrent.atomic.AtomicReferenceFieldUpdater

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

/**
 * Descriptor for multi-word atomic operation.
 * Based on paper
 * ["A Practical Multi-Word Compare-and-Swap Operation"](http://www.cl.cam.ac.uk/research/srg/netos/papers/2002-casn.pdf)
 * by Timothy L. Harris, Keir Fraser and Ian A. Pratt.
 *
 * Note: parts of atomic operation must be globally ordered. Otherwise, this implementation will produce
 * [StackOverflowError].
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public abstract class AtomicOp : OpDescriptor() {
    @Volatile
    private var _consensus: Any? = UNDECIDED

    companion object {
        @JvmStatic
        private val CONSENSUS: AtomicReferenceFieldUpdater<AtomicOp, Any?> =
            AtomicReferenceFieldUpdater.newUpdater(AtomicOp::class.java, Any::class.java, "_consensus")

        private val UNDECIDED: Any = Symbol("UNDECIDED")
    }

    val isDecided: Boolean get() = _consensus !== UNDECIDED

    abstract fun prepare(): Any? // `null` if Ok, or failure reason
    abstract fun complete(affected: Any?, failure: Any?) // failure != null if failed to prepare op

    // returns `null` on success
    final override fun perform(affected: Any?): Any? {
        // make decision on status
        var decision: Any?
        while (true) {
            decision = this._consensus
            if (decision !== UNDECIDED) break
            decision = prepare()
            check(decision !== UNDECIDED)
            if (CONSENSUS.compareAndSet(this, UNDECIDED, decision)) break
        }
        complete(affected, decision)
        return decision
    }
}

/**
 * A part of multi-step atomic operation [AtomicOp].
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
public abstract class AtomicDesc {
    abstract fun prepare(op: AtomicOp): Any? // returns `null` if prepared successfully
    abstract fun complete(op: AtomicOp, failure: Any?) // decision == null if success
}
