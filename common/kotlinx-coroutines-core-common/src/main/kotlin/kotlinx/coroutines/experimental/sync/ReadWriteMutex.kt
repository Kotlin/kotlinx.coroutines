package kotlinx.coroutines.experimental.sync

import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.loop
import kotlinx.coroutines.experimental.internal.*
import kotlinx.coroutines.experimental.selects.SelectClause2
import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED
import kotlin.coroutines.experimental.intrinsics.suspendCoroutineOrReturn

interface ReadWriteMutex {
    val read: Mutex
    val write: Mutex
}

/**
 * Read-write lock for coroutines. This implementation is fair, non-reentrant,
 * and non-suspending when there are no writers.
 */
fun ReadWriteMutex(): ReadWriteMutex = ReadWriteMutexImpl()

private class ReadWriteMutexImpl : ReadWriteMutex {

    // count -1: write lock held
    // count 0: no locks held
    // count x > 0: x read locks held
    // waiters: number of coroutines waiting for a lock
    private class State(val count: Int, val waiters: Int, val owner: Any?)
    private val _state = atomic<Any>(State(0, 0, null)) // S | OpDescriptor

    private class Waiter(val cont: Continuation<Unit>, val isWriter: Boolean, val owner: Any?) :  LockFreeLinkedListNode()
    val queue = LockFreeLinkedListHead() // queue of waiters

    // create an op to atomically enqueue a waiter and increment the waiter count in the state
    private fun createAddWaiterOp(state: State, cont: Continuation<Unit>, isWriter: Boolean, owner: Any?) : OpDescriptor {
        val waiter = Waiter(cont, isWriter, owner)
        val addLastDesc = queue.describeAddLast(waiter)
        return object : AtomicOp<Any?>() {
            override fun prepare(affected: Any?): Any? {
                return addLastDesc.prepare(this)
            }

            override fun complete(affected: Any?, failure: Any?) {
                addLastDesc.complete(this, failure)
                _state.compareAndSet(this, State(state.count, state.waiters + 1, state.owner))
            }
        }
    }

    override val read = object : Mutex {
        override val isLocked: Boolean get() {
            _state.loop { state ->
                when (state) {
                    is OpDescriptor -> state.perform(this) // help
                    is State -> return state.count > 0
                    else -> error("unexpected state $state")
                }
            }
        }

        override fun tryLock(owner: Any?): Boolean {
            require(owner == null) { "owners not supported for read mutex" }
            _state.loop { state ->
                when (state) {
                    is OpDescriptor -> state.perform(this) // help
                    is State -> {
                        if (state.count >= 0 && state.waiters == 0) {
                            if (_state.compareAndSet(state, State(state.count + 1, 0, null))) {
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

        override suspend fun lock(owner: Any?) {
            require(owner == null) { "owners not supported for read mutex" }
            if (tryLock()) return
            else return suspendCoroutineOrReturn { lockCont(it) }
        }

        private fun lockCont(cont: Continuation<Unit>): Any {
            _state.loop { state ->
                when (state) {
                    is OpDescriptor -> state.perform(this) // help
                    is State -> {
                        if (state.count >= 0 && state.waiters == 0) {
                            if (_state.compareAndSet(state, State(state.count + 1, 0, null))) {
                                return Unit
                            }
                        } else {
                            val op = createAddWaiterOp(state, cont, false, null)
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

        override fun unlock(owner: Any?) {
            require(owner == null) { "owners not supported for read mutex" }
            _state.loop { state ->
                when (state) {
                    is OpDescriptor -> state.perform(this) // help
                    is State -> {
                        check(state.count > 0) { "read mutex is not locked" }
                        if (state.count > 1 || state.waiters == 0) {
                            if (_state.compareAndSet(state, State(state.count - 1, state.waiters, null))) {
                                return
                            }
                        } else {
                            // this seems to be the easiest way to peek the queue
                            val waiter = (queue.removeFirstIfIsInstanceOfOrPeekIf<Waiter> { true })!!
                            if (_state.compareAndSet(state, State(-1, state.waiters - 1, waiter.owner))) {
                                val writer = queue.removeFirstOrNull()!! as Waiter
                                writer.cont.resume(Unit)
                                return
                            }
                        }
                    }
                    else -> error("unexpected state $state")
                }
            }
        }

        override val onLock: SelectClause2<Any?, Mutex>
            get() = TODO("support for select is not yet implemented")

        override fun holdsLock(owner: Any): Boolean {
            throw UnsupportedOperationException("owners not supported for read mutex")
        }
    }

    override val write = object : Mutex {
        override val isLocked: Boolean get() {
            _state.loop { state ->
                when (state) {
                    is OpDescriptor -> state.perform(this) // help
                    is State -> return state.count < 0
                    else -> error("unexpected state $state")
                }
            }
        }

        override fun tryLock(owner: Any?): Boolean {
            _state.loop { state ->
                when (state) {
                    is OpDescriptor -> state.perform(this) // help
                    is State -> {
                        if (state.count == 0 && state.waiters == 0) {
                            if (_state.compareAndSet(state, State(-1, 0, owner))) {
                                return true
                            }
                        } else {
                            check(state.owner !== owner) { "already locked by $owner" }
                            return false
                        }
                    }
                    else -> error("unexpected state $state")
                }
            }
        }

        override suspend fun lock(owner: Any?) {
            if (tryLock(owner)) return
            else return suspendCoroutineOrReturn { lockCont(owner, it) }
        }

        private fun lockCont(owner: Any?, cont: Continuation<Unit>): Any {
            _state.loop { state ->
                when (state) {
                    is OpDescriptor -> state.perform(this) // help
                    is State -> {
                        if (state.count == 0 && state.waiters == 0) {
                            if (_state.compareAndSet(state, State(-1, 0, owner))) {
                                return Unit
                            }
                        } else {
                            check(state.owner !== owner) { "already locked by $owner" }
                            val op = createAddWaiterOp(state, cont, true, owner)
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

        override fun unlock(owner: Any?) {
            _state.loop { state ->
                when (state) {
                    is OpDescriptor -> state.perform(this) // help
                    is State -> {
                        check(state.count == -1) { "write mutex is not locked" }
                        check(state.owner === owner) { "write mutex is locked by ${state.owner} but $owner is unlocking it" }
                        if (state.waiters == 0) {
                            if (_state.compareAndSet(state, State(0, 0, null))) {
                                return
                            }
                        } else {
                            // this seems to be the easiest way to peek the queue
                            val waiter = (queue.removeFirstIfIsInstanceOfOrPeekIf<Waiter> { true })!!

                            if (waiter.isWriter) {
                                if (_state.compareAndSet(state, State(-1, state.waiters - 1, waiter.owner))) {
                                    val writer = queue.removeFirstOrNull()!! as Waiter
                                    writer.cont.resume(Unit)
                                    return
                                }
                            } else {
                                var readers = consecutiveWaitingReaderCount()
                                if (_state.compareAndSet(state, State(readers, state.waiters - readers, null))) {
                                    while (readers-- > 0) {
                                        val reader = queue.removeFirstOrNull()!! as Waiter
                                        reader.cont.resume(Unit)
                                    }
                                    return
                                }
                            }
                        }
                    }
                    else -> error("unexpected state $state")
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

        override val onLock: SelectClause2<Any?, Mutex>
            get() = TODO("support for select is not yet implemented")

        override fun holdsLock(owner: Any): Boolean {
            _state.loop { state ->
                when (state) {
                    is OpDescriptor -> state.perform(this) // help
                    is State -> return state.owner === owner
                    else -> error("unexpected $state")
                }
            }
        }
    }
}
