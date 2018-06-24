package kotlinx.coroutines.experimental.sync

import kotlinx.coroutines.experimental.internal.*
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED
import kotlin.coroutines.experimental.intrinsics.suspendCoroutineOrReturn

/**
 * Read-write lock for coroutines. This implementation is fair, non-reentrant,
 * and non-suspending when there are no writers.
 */
class ReadWriteLock {

    // count -1: write lock held
    // count 0: no locks held
    // count x > 0: x read locks held
    // waiters: number of coroutines waiting for a lock
    private class State(val count: Int, val waiters: Int)
    private val sm = StateMachine(State(0, 0))

    private class Waiter(val cont: Continuation<Unit>, val isWriter: Boolean) :  LockFreeLinkedListNode()
    val queue = LockFreeLinkedListHead() // queue of waiters

    suspend fun lockRead() {
        if (tryLockRead()) return
        else return suspendCoroutineOrReturn { lockReadCont(it) }
    }

    fun tryLockRead(): Boolean {
        return sm.transition { state ->
            if (state.count >= 0 && state.waiters == 0) {
                Decision.Move(State(state.count + 1, 0)) { true }
            } else {
                Decision.Stay { false }
            }
        }
    }

    private fun lockReadCont(cont: Continuation<Unit>): Any {
        return sm.transition { state ->
            if (state.count >= 0 && state.waiters == 0) {
                Decision.Move(State(state.count + 1, 0)) { }
            } else {
                val desc = queue.describeAddLast(Waiter(cont, false))
                val nextState = State(state.count, state.waiters + 1)
                Decision.DoAndMove(desc, nextState) {
                    COROUTINE_SUSPENDED
                }
            }
        }
    }

    suspend fun lockWrite() {
        if (tryLockWrite()) return
        else return suspendCoroutineOrReturn { lockWriteCont(it) }
    }

    fun tryLockWrite(): Boolean {
        return sm.transition { state ->
            if (state.count == 0 && state.waiters == 0) {
                Decision.Move(State(-1, 0)) { true }
            } else {
                Decision.Stay { false }
            }
        }
    }

    private fun lockWriteCont(cont: Continuation<Unit>): Any {
        return sm.transition { state ->
            if (state.count == 0 && state.waiters == 0) {
                Decision.Move(State(-1, 0)) { }
            } else {
                val desc = queue.describeAddLast(Waiter(cont, true))
                val nextState = State(state.count, state.waiters + 1)
                Decision.DoAndMove(desc, nextState) {
                    COROUTINE_SUSPENDED
                }
            }
        }
    }

    fun unlockRead() {
        sm.transition { state ->
            if (state.count > 1 || state.waiters == 0) {
                Decision.Move(State(state.count - 1, state.waiters)) { }
            } else {
                Decision.Move(State(-1, state.waiters - 1)) {
                    val writer = queue.removeFirstOrNull()!! as Waiter
                    writer.cont.resume(Unit)
                }
            }
        }
    }

    fun unlockWrite() {
        sm.transition { state ->
            if (state.waiters == 0) {
                Decision.Move(State(0, 0)) { }
            } else {
                // this seems to be the easiest way to peek the queue
                val waiter = (queue.removeFirstIfIsInstanceOfOrPeekIf<Waiter> { true })!!

                if (waiter.isWriter) {
                    Decision.Move(State(-1, state.waiters - 1)) {
                        val writer = queue.removeFirstOrNull()!! as Waiter
                        writer.cont.resume(Unit)
                    }
                } else {
                    var readers = consecutiveWaitingReaderCount()
                    Decision.Move(State(readers, state.waiters - readers)) {
                        while (readers-- > 0) {
                            val reader = queue.removeFirstOrNull()!! as Waiter
                            reader.cont.resume(Unit)
                        }
                    }
                }
            }
        }
    }

    private fun consecutiveWaitingReaderCount(): Int {
        var readers = 0
        var done = false
        queue.forEach<Waiter> { waiter ->
            if (waiter.isWriter) {
                done = true // TODO: terminate iteration early somehow
            } else if (!done) {
                readers++
            }
        }
        return readers
    }
}
