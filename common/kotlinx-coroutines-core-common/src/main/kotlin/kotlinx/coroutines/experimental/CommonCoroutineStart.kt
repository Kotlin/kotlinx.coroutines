package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.Continuation

public expect enum class CoroutineStart {
    DEFAULT,
    LAZY,
    ATOMIC,
    UNDISPATCHED;
    public operator fun <T> invoke(block: suspend () -> T, completion: Continuation<T>)
    public operator fun <R, T> invoke(block: suspend R.() -> T, receiver: R, completion: Continuation<T>)
    public val isLazy: Boolean
}
