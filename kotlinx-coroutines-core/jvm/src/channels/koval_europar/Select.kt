/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.channels.koval_europar

import kotlinx.atomicfu.atomic
import kotlinx.coroutines.*
import java.util.*
import kotlin.coroutines.Continuation

public suspend inline fun <R> selectEuropar(crossinline builder: SelectBuilder<R>.() -> Unit): R {
    val select = SelectInstance<R>()
    val result = suspendCancellableCoroutine<Any?> { curCont ->
        select.cont = curCont
        builder(select)
    }
    return select.completeSelect(result)
}

public interface SelectBuilder<RESULT> {
    public operator fun <FUNC_RESULT> Param0RegInfo<FUNC_RESULT>.invoke(block: (FUNC_RESULT) -> RESULT)

    public operator fun <PARAM, FUNC_RESULT> Param1RegInfo<FUNC_RESULT>.invoke(param: PARAM, block: (FUNC_RESULT) -> RESULT)
    public operator fun <FUNC_RESULT> Param1RegInfo<FUNC_RESULT>.invoke(block: (FUNC_RESULT) -> RESULT): Unit = invoke(null, block)
}

// channel, selectInstance, element -> is selected by this alternative
@UseExperimental(InternalCoroutinesApi::class)
public typealias RegFunc = Function3<RendezvousChannelEuropar<*>, SelectInstance<*>, Any?, Unit>
public class Param0RegInfo<FUNC_RESULT>(channel: Any, regFunc: RegFunc, actFunc: ActFunc<FUNC_RESULT>)
    : RegInfo<FUNC_RESULT>(channel, regFunc, actFunc)
public class Param1RegInfo<FUNC_RESULT>(channel: Any, regFunc: RegFunc, actFunc: ActFunc<FUNC_RESULT>)
    : RegInfo<FUNC_RESULT>(channel, regFunc, actFunc)

public abstract class RegInfo<FUNC_RESULT>(
    @JvmField public val channel: Any,
    @JvmField public val regFunc: RegFunc,
    @JvmField public val actFunc: ActFunc<FUNC_RESULT>
)
// continuation, result (usually a received element), block
public typealias ActFunc<FUNC_RESULT> = Function2<Any?, Function1<FUNC_RESULT, Any?>, Any?>
@InternalCoroutinesApi
public class SelectInstance<RESULT> : SelectBuilder<RESULT> {
    public val id: Long = selectInstanceIdGenerator.incrementAndGet()
    private val alternatives = ArrayList<Any?>(ALTERNATIVE_SIZE * 2)

    private val _state = atomic<Any?>(null)

    public lateinit var cont: CancellableContinuation<in Any?>

    public var cleanable: Cleanable? = null
    public var index: Int = 0

    public fun setState(state: Any) { _state.value = state }

    override fun <FUNC_RESULT> Param0RegInfo<FUNC_RESULT>.invoke(block: (FUNC_RESULT) -> RESULT) {
        addAlternative(this, null, block)
    }
    override fun <PARAM, FUNC_RESULT> Param1RegInfo<FUNC_RESULT>.invoke(param: PARAM, block: (FUNC_RESULT) -> RESULT) {
        addAlternative(this, param, block)
    }
    private fun <FUNC_RESULT> addAlternative(regInfo: RegInfo<*>, param: Any?, block: (FUNC_RESULT) -> RESULT) {
        if (isSelected()) return
        val regFunc = regInfo.regFunc
        val channel = regInfo.channel as RendezvousChannelEuropar<*> // todo FIX TYPES
        regFunc(channel, this, param)
        if (cleanable == null) {
            alternatives.add(regInfo)
            alternatives.add(block)
            alternatives.add(null)
            alternatives.add(null)
        } else {
            alternatives.add(regInfo)
            alternatives.add(block)
            alternatives.add(index)
            alternatives.add(cleanable)
        }
    }
    /**
     * Shuffles alternatives for [selectUnbiased].
     */
    public fun shuffleAlternatives() {
    }
    /**
     * Performs `select` in 3-phase way. At first it selects an alternative atomically
     * (suspending if needed), then it unregisters from unselected channels,
     * and invokes the specified for the selected alternative action at last.
     */
    public suspend fun completeSelect(result: Any?): RESULT {
        cleanNonSelectedAlternatives()
        return invokeSelectedAlternativeAction(result)
    }


    public fun isSelected(): Boolean = readState(null) != null
    private fun readState(allowedUnprocessedDesc: Any?): Any? {
        while (true) { // CAS loop
            val state = _state.value
            if (state === null || state === allowedUnprocessedDesc || state !is SelectDesc)
                return state
            if (state.invoke()) {
                return state
            } else if (_state.compareAndSet(state, null)) {
                return null
            }
        }
    }
    public fun trySetDescriptor(desc: Any): Boolean {
        while (true) {
            val state = readState(desc)
            if (state === desc) return true
            if (state != null) return false
            if (_state.compareAndSet(null, desc)) return true
        }
    }
    public fun resetState(desc: Any) {
        _state.compareAndSet(desc, null)
    }


    /**
     * This function removes this `SelectInstance` from the
     * waiting queues of other alternatives.
     */
    public fun cleanNonSelectedAlternatives() {
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            val cleanable = alternatives[i + 3]
            val index = alternatives[i + 2]
            // `cleanable` can be null in case this alternative has not been processed.
            // This means that the next alternatives has not been processed as well.
            if (cleanable === null) break
            cleanable as Cleanable
            cleanable.clean(index as Int)
        }
    }
    /**
     * Gets the act function and the block for the selected alternative and invoke it
     * with the specified result.
     */
    private fun invokeSelectedAlternativeAction(result: Any?): RESULT {
        val i = selectedAlternativeIndex()
        val actFunc = (alternatives[i] as RegInfo<*>).actFunc as ActFunc<in Any>
        val block = alternatives[i + 1] as (Any?) -> RESULT
        return actFunc(result, block) as RESULT
    }
    /**
     * Return an index of the selected alternative in `alternatives` array.
     */
    private fun selectedAlternativeIndex(): Int {
        val channel = _state.value!!
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            val ch = if (channel is SelectDesc) channel.channel else channel
            if ((alternatives[i] as RegInfo<*>).channel === ch) return i
        }
        error("Channel $channel is not found")
    }

    private companion object {
        private val selectInstanceIdGenerator = java.util.concurrent.atomic.AtomicLong(0L)
        // Number of items to be stored for each alternative in `alternatives` array.
        const val ALTERNATIVE_SIZE = 4
    }
}


public class SelectDesc constructor(@JvmField public val channel: Any, @JvmField public val selectInstance: SelectInstance<*>, @JvmField public val anotherCont: Any) {
    @Volatile private var _status: Byte = STATUS_UNDECIDED
    @InternalCoroutinesApi
    public fun invoke(): Boolean {
        // Optimization: check this descriptor's status.
        val status = _status
        if (status != STATUS_UNDECIDED) return status == STATUS_SUCCEED
        // Set the descriptor to `SelectInstance`s.
        var failed = false
        if (anotherCont is SelectInstance<*>) {
            if (selectInstance.id < anotherCont.id) {
                if (selectInstance.trySetDescriptor(this)) {
                    if (!anotherCont.trySetDescriptor(this)) {
                        failed = true
                        selectInstance.resetState(this)
                    }
                } else { failed = true }
            } else {
                if (anotherCont.trySetDescriptor(this)) {
                    if (!selectInstance.trySetDescriptor(this)) {
                        failed = true
                        anotherCont.resetState(this)
                    }
                } else { failed = true }
            }
        } else {
            anotherCont as CancellableContinuation<*>
            if (!selectInstance.trySetDescriptor(this)) {
                failed = true
            }
        }
        // Check if failed
        if (failed) {
            _status = STATUS_FAILED
            return false
        } else {
            _status = STATUS_SUCCEED
            return true
        }
    }
    private companion object {
        const val STATUS_UNDECIDED: Byte = 0
        const val STATUS_SUCCEED: Byte = 1
        const val STATUS_FAILED: Byte = 2
    }
}