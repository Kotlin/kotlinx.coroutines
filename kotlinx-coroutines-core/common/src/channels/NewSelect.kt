package kotlinx.coroutines.channels

import kotlinx.atomicfu.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.Symbol
import kotlinx.coroutines.selects.*
import kotlin.coroutines.*
import kotlin.math.*
import kotlin.native.concurrent.*


public suspend inline fun <R> newSelect(crossinline builder: NewSelectBuilder<R>.() -> Unit): R =
    NewSelectBuilderImpl<R>().run {
        builder(this)
        doSelect()
    }

public suspend inline fun <R> newSelectUnbiased(crossinline builder: NewSelectBuilder<R>.() -> Unit): R =
    NewSelectBuilderImpl<R>().run {
        builder(this)
        unbiased = true
        doSelect()
    }

/**
 * Scope for [select] invocation.
 */
public interface NewSelectBuilder<in R> {
    /**
     * If set to `true` this `select` expression randomly shuffles the clauses before checking if they are selectable,
     * thus ensuring that there is no statistical bias to the selection of the first clauses.
     */
    public var unbiased: Boolean

    /**
     * Registers clause in this [select] expression without additional parameters that does not select any value.
     */
    public operator fun NewSelectClause0.invoke(block: suspend () -> R)

    /**
     * Registers clause in this [select] expression without additional parameters that selects value of type [Q].
     */
    public operator fun <Q> NewSelectClause1<Q>.invoke(block: suspend (Q) -> R)

    /**
     * Registers clause in this [select] expression with additional parameter of type [P] that selects value of type [Q].
     */
    public operator fun <P, Q> NewSelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R)

    /**
     * Registers clause in this [select] expression with additional parameter nullable parameter of type [P]
     * with the `null` value for this parameter that selects value of type [Q].
     */
    public operator fun <P, Q> NewSelectClause2<P?, Q>.invoke(block: suspend (Q) -> R): Unit = invoke(null, block)

    /**
     * Clause that selects the given [block] after a specified timeout passes.
     * If timeout is negative or zero, [block] is selected immediately.
     *
     * **Note: This is an experimental api.** It may be replaced with light-weight timer/timeout channels in the future.
     *
     * @param timeMillis timeout time in milliseconds.
     */
    @ExperimentalCoroutinesApi
    public fun onTimeout(timeMillis: Long, block: suspend () -> R)
}

/**
 * Clause for [select] expression without additional parameters that does not select any value.
 */
public interface NewSelectClause0 : NewSelectClause

@InternalCoroutinesApi
public class NewSelectClause0Impl(
    override val objForSelect: Any,
    override val regFunc: RegistrationFunction,
    override val processResFunc: ProcessResultFunction
) : NewSelectClause0

/**
 * Clause for [select] expression without additional parameters that selects value of type [Q].
 */
public interface NewSelectClause1<out Q> : NewSelectClause

@InternalCoroutinesApi
public class NewSelectClause1Impl<Q>(
    override val objForSelect: Any,
    override val regFunc: RegistrationFunction,
    override val processResFunc: ProcessResultFunction
) : NewSelectClause1<Q>

/**
 * Clause for [select] expression with additional parameter of type [P] that selects value of type [Q].
 */
public interface NewSelectClause2<in P, out Q> : NewSelectClause

@InternalCoroutinesApi
public class NewSelectClause2Impl<P, Q>(
    override val objForSelect: Any,
    override val regFunc: RegistrationFunction,
    override val processResFunc: ProcessResultFunction
) : NewSelectClause2<P, Q>

@InternalCoroutinesApi
public interface NewSelectClause {
    public val objForSelect: Any
    public val regFunc: RegistrationFunction
    public val processResFunc: ProcessResultFunction
}

public typealias RegistrationFunction = (objForSelect: Any, select: NewSelectInstance<*>, param: Any?) -> Unit
public typealias ProcessResultFunction = (objForSelect: Any, param: Any?, selectResult: Any?) -> Any?
public typealias OnCompleteAction = () -> Unit

/**
 * Internal representation of select instance. This instance is called _selected_ when
 * the clause to execute is already picked.
 *
 * @suppress **This is unstable API and it is subject to change.**
 */
@InternalCoroutinesApi
public interface NewSelectInstance<in R> {
    /**
     * An unique integer id
     */
    public val id: Long

    /**
     * If this `select` operation is trying to make a rendezvous with another `select` operation which is in the
     * `WAITING` phase, it should store this another `select` operation into this field. It is required to be able
     * to find and resolve deadlocks.
     */
    public var waitingFor: NewSelectInstance<*>?

    /**
     * This function should be called by other operations which are trying to perform a rendezvous with this `select`.
     * If this another operation is [SelectInstance] then it should be passed as [from] parameter. Returns `true` if
     * the rendezvous succeeds, `false` otherwise.
     */
    public fun trySelect(objForSelect: Any, result: Any?, from: NewSelectInstance<*>? = null): Boolean

    /**
     * This function should be called if this `select` is registered as a waiter. A function which removes the waiter
     * after this `select` is processed should be provided as a parameter.
     */
    public fun invokeOnCompletion(onCompleteAction: () -> Unit)

    /**
     * This function should be called during this `select` registration phase on a successful rendezvous.
     */
    public fun selectInRegPhase(selectResult: Any?)
}

@SharedImmutable
internal val ALREADY_SELECTED: Any = Symbol("ALREADY_SELECTED")
@SharedImmutable
private val UNDECIDED: Any = Symbol("UNDECIDED")
@SharedImmutable
private val RESUMED: Any = Symbol("RESUMED")

@PublishedApi
internal class NewSelectBuilderImpl<R> : NewSelectBuilder<R>, NewSelectInstance<R> {
    lateinit var cont: CancellableContinuation<Any?>
    override val id = ID_GENERATOR.getAndIncrement()
    override var waitingFor: NewSelectInstance<*>? = null
    override var unbiased: Boolean = false

    // TODO bridge with old SelectBuilderImpl (getResult + handleException + constructor) + test

    // 0: objForSelect
    // 1: RegistrationFunction
    // 2: ProcessResultFunction
    // 3: param
    // 4: block
    // 5: onCompleteAction
    private val alternatives = ArrayList<Any?>(ALTERNATIVE_SIZE * 2) // 2 clauses -- the most common case

    private var resultOrOnCompleteAction: Any? = null
    private val state = atomic<Any?>(STATE_REG)

    override fun invokeOnCompletion(onCompleteAction: () -> Unit) {
        resultOrOnCompleteAction = onCompleteAction
    }

    override fun selectInRegPhase(selectResult: Any?) {
        state.value = STATE_DONE
        resultOrOnCompleteAction = selectResult
    }

    suspend fun doSelect(): R {
        if (unbiased) shuffleAlternatives()
        val resumeResult = try {
            selectAlternative()
        } catch (e: Throwable) {
            cleanState()
            cleanNonSelectedAlternatives(-1)
            throw e
        }
        val i = selectedAlternativeIndex(state.value!!)
        cleanNonSelectedAlternatives(i)
        cleanState()
        val result = processResult(i, resumeResult)
        return invokeSelectedAlternativeAction<R>(i, result).also { alternatives.clear() }
    }

    private fun cleanState() {
        state.value = STATE_DONE
    }

    private fun processResult(i: Int, resumeResult: Any?): Any? {
        val objForSelect = alternatives[i]!!
        val processResFunc = alternatives[i + 2] as ProcessResultFunction
        val param = alternatives[i + 3]
        return processResFunc(objForSelect, param, resumeResult)
    }

    internal fun addAlternative(objForSelect: Any, regFunc: RegistrationFunction, processResFunc: ProcessResultFunction, param: Any?, block: Any) {
        alternatives.add(objForSelect)
        alternatives.add(regFunc)
        alternatives.add(processResFunc)
        alternatives.add(param)
        alternatives.add(block)
        alternatives.add(null)
    }

    /**
     * Shuffles alternatives for the _unbiased_ mode.
     */
    private fun shuffleAlternatives() {
        // TODO implement me
        // Random.nextInt()
    }

    suspend fun selectAlternative(): Any? {
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            val objForSelect = alternatives[i]!!
            val regFunc = alternatives[i + 1] as RegistrationFunction
            val param = alternatives[i + 3]
            regFunc(objForSelect, this, param)
            if (state.value === STATE_REG) {
                // successfully registered
                alternatives[i + 5] = resultOrOnCompleteAction.also { resultOrOnCompleteAction = null }
            } else {
                state.value = objForSelect
                // rendezvous happened
                return resultOrOnCompleteAction.also { resultOrOnCompleteAction = null }
            }
        }
        return suspendCancellableCoroutineReusable { cont ->
            this.cont = cont
            while (true) {
                val objForSelect = extractFromStackOrClose() ?: break
                val i = selectedAlternativeIndex(objForSelect)
                // Try to register again
                val regFunc = alternatives[i + 1] as RegistrationFunction
                val param = alternatives[i + 3]
                regFunc(objForSelect, this, param)
                if (state.value === STATE_REG) {
                    // successfully registered
                    alternatives[i + 5] = resultOrOnCompleteAction.also { resultOrOnCompleteAction = null }
                } else {
                    state.value = objForSelect
                    // rendezvous happened
                    val res = resultOrOnCompleteAction.also { resultOrOnCompleteAction = null }
                    cont.resume(res)
                    break
                }
            }
            state.compareAndSet(STATE_REG, STATE_WAITING)
        }
    }

    /**
     * This function removes this `SelectInstance` from the
     * waiting queues of other alternatives.
     */
    fun cleanNonSelectedAlternatives(selectedIndex: Int) {
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            if (i / ALTERNATIVE_SIZE == selectedIndex) continue
            val onCompleteAction = alternatives[i + 5] as OnCompleteAction?
            onCompleteAction?.invoke()
        }
    }
    /**
     * Gets the act function and the block for the selected alternative and invoke it
     * with the specified result.
     */
    suspend fun <R> invokeSelectedAlternativeAction(i: Int, result: Any?): R {
        val param = alternatives[i + 3]
        val block = alternatives[i + 4]
        return if (param === PARAM_CLAUSE_0) {
            block as suspend () -> R
            block()
        } else {
            block as suspend (Any?) -> R
            block(result)
        }
    }

    /**
     * Return an index of the selected alternative in `alternatives` array.
     */
    private fun selectedAlternativeIndex(objForSelect: Any): Int {
        for (i in 0 until alternatives.size step ALTERNATIVE_SIZE) {
            if (alternatives[i] === objForSelect) return i
        }
        error("Object for select $objForSelect is not found")
    }

    override fun trySelect(objForSelect: Any, result: Any?, from: NewSelectInstance<*>?): Boolean {
        from?.waitingFor = this
        try {
            var curState: Any? = this.state.value
            var t = 0
            while (curState === STATE_REG) {
                if (from != null && shouldBreakDeadlock(from, from, from.id)) return false
                if (true || ++t == 128) {
                    if (reregisterSelect(objForSelect)) {
                        return false
                    } else {
                        state.compareAndSet(STATE_REG, STATE_WAITING)
                    }
                }
                curState = this.state.value
            }
            if (curState != STATE_WAITING) return false
            if (!state.compareAndSet(STATE_WAITING, objForSelect)) return false
            val resumeToken = cont.tryResume(result) ?: return false
            cont.completeResume(resumeToken)
            return true
        } finally {
            from?.waitingFor = null
        }
    }

    private class Node(val objForSelect: Any?, val next: Node?)
    private val stack = atomic<Node?>(null)
    private val CLOSED = Node(null, null)

    private fun reregisterSelect(objForSelect: Any): Boolean {
        stack.loop { cur ->
            if (cur === CLOSED) return false
            if (stack.compareAndSet(cur, Node(objForSelect, cur))) return true
        }
    }
    private fun extractFromStackOrClose(): Any? {
        stack.loop { cur ->
            if (cur === null) {
                if (stack.compareAndSet(null, CLOSED)) return null
            } else {
                if (stack.compareAndSet(cur, cur.next)) return cur.objForSelect
            }
        }
    }

    private fun shouldBreakDeadlock(start: NewSelectInstance<*>, cur: NewSelectInstance<*>, curMin: Long): Boolean {
        val next = cur.waitingFor ?: return false
        val newMin = min(curMin, next.id)
        if (next === start) return newMin == start.id
        return shouldBreakDeadlock(start, next, newMin)
    }

    override fun NewSelectClause0.invoke(block: suspend () -> R) =
        addAlternative(objForSelect, regFunc, processResFunc, PARAM_CLAUSE_0, block)

    override fun <Q> NewSelectClause1<Q>.invoke(block: suspend (Q) -> R) =
        addAlternative(objForSelect, regFunc, processResFunc, PARAM_CLAUSE_1, block)

    override fun <P, Q> NewSelectClause2<P, Q>.invoke(param: P, block: suspend (Q) -> R) =
        addAlternative(objForSelect, regFunc, processResFunc, param, block)

    override fun onTimeout(timeMillis: Long, block: suspend () -> R) = TODO("Not supported yet")
}

private val ID_GENERATOR = atomic(0L)
// Number of items to be stored for each alternative in the `alternatives` array.
private const val ALTERNATIVE_SIZE = 6

private val STATE_REG = Symbol("STATE_REG")
private val STATE_WAITING = Symbol("STATE_WAITING")
private val STATE_DONE = Symbol("STATE_DONE")

internal val PARAM_CLAUSE_0 = Symbol("PARAM_CLAUSE_0")
private val PARAM_CLAUSE_1 = Symbol("PARAM_CLAUSE_1")