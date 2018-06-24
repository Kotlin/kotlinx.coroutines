package kotlinx.coroutines.experimental.sync

import kotlinx.coroutines.experimental.internal.*
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED
import kotlin.coroutines.experimental.intrinsics.suspendCoroutineOrReturn

/**
 * Counting semaphore for coroutines. This implementation is fair and
 * non-suspending when permits are available.
 */
class Semaphore(initialPermits: Int) {

    // permits: number of permits available to be acquired
    // waiters: number of coroutines waiting to acquire permits
    private class State(val permits: Int, val waiters: Int)
    private val sm = StateMachine(State(initialPermits, 0))

    private class Waiter(val cont: Continuation<Unit>) :  LockFreeLinkedListNode()
    val queue = LockFreeLinkedListHead() // queue of waiters

    suspend fun acquire() {
        if (tryAcquire()) return
        else return suspendCoroutineOrReturn { acquireCont(it) }
    }

    fun tryAcquire(): Boolean {
        return sm.transition { state ->
            if (state.permits > 0 && state.waiters == 0) {
                Decision.Move(State(state.permits - 1, 0)) { true }
            } else {
                Decision.Stay { false }
            }
        }
    }

    private fun acquireCont(cont: Continuation<Unit>): Any {
        return sm.transition { state ->
            if (state.permits > 0 && state.waiters == 0) {
                Decision.Move(State(state.permits - 1, 0)) { }
            } else {
                val desc = queue.describeAddLast(Waiter(cont))
                val nextState = State(state.permits, state.waiters + 1)
                Decision.DoAndMove(desc, nextState) {
                    COROUTINE_SUSPENDED
                }
            }
        }
    }

    fun release() {
        return sm.transition { state ->
            if (state.permits < 0 || state.waiters == 0) {
                Decision.Move(State(state.permits + 1, state.waiters)) { }
            } else {
                Decision.Move(State(state.permits, state.waiters - 1)) {
                    val waiter = queue.removeFirstOrNull()!! as Waiter
                    waiter.cont.resume(Unit)
                }
            }
        }
    }
}
