package kotlinx.coroutines.experimental.sync

import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.loop
import kotlinx.coroutines.experimental.internal.*
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED
import kotlin.coroutines.experimental.intrinsics.suspendCoroutineOrReturn

interface Semaphore {
    val permits: Int
    fun tryAcquire(): Boolean
    suspend fun acquire()
    fun release()
}

/**
 * Counting semaphore for coroutines. This implementation is fair and
 * non-suspending when permits are available.
 */
fun Semaphore(initialPermits: Int): Semaphore = SemaphoreImpl(initialPermits)

private class SemaphoreImpl(initialPermits: Int) : Semaphore {

    // permits: number of permits available to be acquired
    // waiters: number of coroutines waiting to acquire permits
    private class State(val permits: Int, val waiters: Int)
    private val _state = atomic<Any>(State(initialPermits, 0)) // S | OpDescriptor

    private class Waiter(val cont: Continuation<Unit>) :  LockFreeLinkedListNode()
    val queue = LockFreeLinkedListHead() // queue of waiters

    // create an op to atomically enqueue a waiter and increment the waiter count in the state
    private fun createAddWaiterOp(state: State, cont: Continuation<Unit>) : OpDescriptor {
        val waiter = Waiter(cont)
        val addLastDesc = queue.describeAddLast(waiter)
        return object : AtomicOp<Any?>() {
            override fun prepare(affected: Any?): Any? {
                return addLastDesc.prepare(this)
            }

            override fun complete(affected: Any?, failure: Any?) {
                addLastDesc.complete(this, failure)
                _state.compareAndSet(this, State(state.permits, state.waiters + 1))
            }
        }
    }

    override val permits: Int get() {
        _state.loop { state ->
            when (state) {
                is OpDescriptor -> state.perform(this) // help
                is State -> return state.permits
                else -> error("unexpected state $state")
            }
        }
    }

    override suspend fun acquire() {
        if (tryAcquire()) return
        else return suspendCoroutineOrReturn { acquireCont(it) }
    }

    override fun tryAcquire(): Boolean {
        _state.loop { state ->
            when (state) {
                is OpDescriptor -> state.perform(this) // help
                is State -> {
                    if (state.permits > 0 && state.waiters == 0) {
                        if (_state.compareAndSet(state, State(state.permits - 1, 0))) {
                            return true
                        }
                    } else {
                        return false
                    }
                }
                else -> error("unexpected state $state")
            }
        }
    }

    private fun acquireCont(cont: Continuation<Unit>): Any {
        _state.loop { state ->
            when (state) {
                is OpDescriptor -> state.perform(this) // help
                is State -> {
                    if (state.permits > 0 && state.waiters == 0) {
                        if (_state.compareAndSet(state, State(state.permits - 1, 0))) {
                            return Unit
                        }
                    } else {
                        val op = createAddWaiterOp(state, cont)
                        if (_state.compareAndSet(state, op)) {
                            op.perform(this)
                            return COROUTINE_SUSPENDED
                        }
                    }
                }
                else -> error("unexpected state $state")
            }
        }
    }

    override fun release() {
        _state.loop { state ->
            when (state) {
                is OpDescriptor -> state.perform(this) // help
                is State -> {
                    if (state.permits < 0 || state.waiters == 0) {
                        if (_state.compareAndSet(state, State(state.permits + 1, state.waiters))) {
                            return
                        }
                    } else {
                        if (_state.compareAndSet(state, State(state.permits, state.waiters - 1))) {
                            val waiter = queue.removeFirstOrNull()!! as Waiter
                            waiter.cont.resume(Unit)
                            return
                        }
                    }
                }
                else -> error("unexpected state $state")
            }
        }
    }
}
