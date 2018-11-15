package channels_new

import kotlinx.atomicfu.atomic
import kotlinx.coroutines.CancellableContinuation
import java.util.*
import java.util.concurrent.atomic.AtomicLong
import kotlin.coroutines.Continuation
import kotlin.coroutines.suspendCoroutine

suspend inline fun <R> select(crossinline builder: SelectBuilder<R>.() -> Unit): R {
    val select = SelectInstance<R>()
    builder(select)
    return select.select()
}

suspend inline fun <R> selectUnbiased(crossinline builder: SelectBuilder<R>.() -> Unit): R {
    val select = SelectInstance<R>()
    builder(select)
    select.shuffleAlternatives()
    return select.select()
}

interface SelectBuilder<RESULT> {
    operator fun <FUNC_RESULT> Param0RegInfo<FUNC_RESULT>.invoke(block: (FUNC_RESULT) -> RESULT)

    operator fun <PARAM, FUNC_RESULT> Param1RegInfo<FUNC_RESULT>.invoke(param: PARAM, block: (FUNC_RESULT) -> RESULT)
    operator fun <FUNC_RESULT> Param1RegInfo<FUNC_RESULT>.invoke(block: (FUNC_RESULT) -> RESULT) = invoke(null, block)
}

// channel, selectInstance, element -> is selected by this alternative
typealias RegFunc = Function3<RendezvousChannel<*>, SelectInstance<*>, Any?, RegResult?>
class Param0RegInfo<FUNC_RESULT>(
        @JvmField val channel: Any,
        @JvmField val regFunc: RegFunc,
        @JvmField val actFunc: ActFunc<FUNC_RESULT>
)
class Param1RegInfo<FUNC_RESULT>(
        @JvmField val channel: Any,
        @JvmField val regFunc: RegFunc,
        @JvmField val actFunc: ActFunc<FUNC_RESULT>
)
class RegResult(@JvmField val cleanable: Cleanable, @JvmField val index: Int)
// continuation, result (usually a received element), block
typealias ActFunc<FUNC_RESULT> = Function2<Any?, Function1<FUNC_RESULT, Any?>, Any?>
class SelectInstance<RESULT> : SelectBuilder<RESULT> {
    @JvmField val id = selectInstanceIdGenerator.incrementAndGet()
    private val alternatives = ArrayList<Any?>()
    lateinit var cont: Continuation<in Any>
    private val _state = atomic<Any?>(null)
    override fun <FUNC_RESULT> Param0RegInfo<FUNC_RESULT>.invoke(block: (FUNC_RESULT) -> RESULT) {
        addAlternative(channel, null, regFunc, actFunc, block)
    }
    override fun <PARAM, FUNC_RESULT> Param1RegInfo<FUNC_RESULT>.invoke(param: PARAM, block: (FUNC_RESULT) -> RESULT) {
        addAlternative(channel, param, regFunc, actFunc, block)
    }
    private fun <FUNC_RESULT> addAlternative(channel: Any, param: Any?, regFunc: Any, actFunc: ActFunc<FUNC_RESULT>, block: (FUNC_RESULT) -> RESULT) {
        alternatives.add(channel)
        alternatives.add(param)
        alternatives.add(regFunc)
        alternatives.add(actFunc)
        alternatives.add(block)
        alternatives.add(null)
        alternatives.add(null)
    }
    /**
     * Shuffles alternatives for [selectUnbiased].
     */
    fun shuffleAlternatives() {
        // This code is based on `Collections#shuffle`,
        // just adapted to our purposes only.
//        val size = alternatives.size / ALTERNATIVE_SIZE
//        for (i in size - 1 downTo 1) {
//            val j = ThreadLocalRandom.current().nextInt(i + 1)
//            for (offset in 0 until ALTERNATIVE_SIZE) {
//                Collections.swap(alternatives, i * ALTERNATIVE_SIZE + offset, j * ALTERNATIVE_SIZE + offset)
//            }
//        }
    }
    /**
     * Performs `select` in 3-phase way. At first it selects an alternative atomically
     * (suspending if needed), then it unregisters from unselected channels,
     * and invokes the specified for the selected alternative action at last.
     */
    suspend fun select(): RESULT {
        val result = selectAlternative()
        cleanNonSelectedAlternatives()
        return invokeSelectedAlternativeAction(result)
    }
    /**
     * After this function is invoked it is guaranteed that an alternative is selected
     * and the corresponding channel is stored into `_state` field.
     */
    private suspend fun selectAlternative(): Any? = suspendCoroutine sc@ { curCont ->
        this.cont = curCont
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            val channel = alternatives[i]!!
            val param = alternatives[i + 1]
            val regFunc = alternatives[i + 2]
            regFunc as RegFunc
            channel as RendezvousChannel<*> // todo FIX TYPES
            val regResult = regFunc(channel, this, param)
            if (regResult != null) {
                alternatives[i + 6] = regResult.index
                alternatives[i + 5] = regResult.cleanable
            }
            if (isSelected()) return@sc
        }
    }
    fun isSelected(): Boolean = readState(null) != null
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
    fun trySetDescriptor(desc: Any): Boolean {
        while (true) {
            val state = readState(desc)
            if (state === desc) return true
            if (state != null) return false
            if (_state.compareAndSet(null, desc)) return true
        }
    }
    fun resetState(desc: Any) {
        _state.compareAndSet(desc, null)
    }
    /**
     * This function removes this `SelectInstance` from the
     * waiting queues of other alternatives.
     */
    private fun cleanNonSelectedAlternatives() {
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            val cleanable = alternatives[i + 5]
            val index = alternatives[i + 6]
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
        val actFunc = alternatives[i + 3] as ActFunc<in Any>
        val block = alternatives[i + 4] as (Any?) -> RESULT
        return actFunc(result, block) as RESULT
    }
    /**
     * Return an index of the selected alternative in `alternatives` array.
     */
    private fun selectedAlternativeIndex(): Int {
        val state = _state.value!!
        val channel = if (state is SelectDesc) state.channel else state
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            if (alternatives[i] === channel) return i
        }
        error("Channel $channel is not found")
    }
    companion object {
        @JvmStatic private val selectInstanceIdGenerator = AtomicLong()
        // Number of items to be stored for each alternative in `alternatives` array.
        const val ALTERNATIVE_SIZE = 7
    }
}
class SelectDesc(@JvmField val channel: Any, @JvmField val selectInstance: SelectInstance<*>, @JvmField val anotherCont: Any) {
    @JvmField @Volatile var _status: Byte = STATUS_UNDECIDED
    fun invoke(): Boolean {
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
    companion object {
        const val STATUS_UNDECIDED: Byte = 0
        const val STATUS_SUCCEED: Byte = 1
        const val STATUS_FAILED: Byte = 2
    }
}