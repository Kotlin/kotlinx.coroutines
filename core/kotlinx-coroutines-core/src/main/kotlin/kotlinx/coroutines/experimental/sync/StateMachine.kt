package kotlinx.coroutines.experimental.sync

import kotlinx.atomicfu.atomic
import kotlinx.atomicfu.loop
import kotlinx.coroutines.experimental.internal.AtomicDesc
import kotlinx.coroutines.experimental.internal.AtomicOp
import kotlinx.coroutines.experimental.internal.OpDescriptor

/**
 * A general non-blocking state machine. Supports performing an AtomicDesc
 * atomically along with a state change.
 */
internal class StateMachine<S : Any>(initialState: S) {

    private val _state = atomic<Any>(initialState) // S | OpDescriptor

    /**
     * Gets a decision on what state change to make from the client based on
     * the current state. Handles helping OpDescriptors and optimistic
     * concurrency retries in the case of conflicting state changes.
     */
    fun <T> transition(decider: (S) -> Decision<S, T>): T {
        _state.loop { state ->
            when (state) {
                is OpDescriptor -> state.perform(this) // help
                else -> { // must be S but can't check it
                    state as S
                    val decision = decider.invoke(state)
                    when (decision) {
                        is Decision.Stay -> {
                            return decision.onSuccess.invoke()
                        }
                        is Decision.Move -> {
                            if (_state.compareAndSet(state, decision.state)) {
                                return decision.onSuccess.invoke()
                            }
                        }
                        is Decision.DoAndMove -> {
                            val op = DoAndMoveOp(decision.desc, decision.state)
                            if (_state.compareAndSet(state, op)) {
                                op.perform(this)
                                return decision.onSuccess.invoke()
                            }
                        }
                    }
                }
            }
        }
    }

    inner class DoAndMoveOp(private val desc: AtomicDesc, private val targetState: S) : AtomicOp<Any?>() {
        override fun prepare(affected: Any?): Any? {
            return desc.prepare(this)
        }

        override fun complete(affected: Any?, failure: Any?) {
            desc.complete(this, failure)
            _state.compareAndSet(this, targetState)
        }
    }
}

internal sealed class Decision<out S, out T> {
    // don't change the state
    class Stay<out T>(val onSuccess: () -> T) : Decision<Nothing, T>()
    // just change the state
    class Move<out S, out T>(val state: S, val onSuccess: () -> T) : Decision<S, T>()
    // do something and change the state, atomically
    class DoAndMove<out S, out T>(val desc: AtomicDesc, val state: S, val onSuccess: () -> T) : Decision<S, T>()
}
