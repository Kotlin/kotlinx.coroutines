package kotlinx.coroutines.experimental.intrinsics

import kotlin.coroutines.experimental.Continuation
import kotlin.coroutines.experimental.intrinsics.COROUTINE_SUSPENDED

/**
 * Starts coroutine without receiver and with result type [T].
 * This function creates and start a new, fresh instance of suspendable computation every time it is invoked.
 * If the coroutine never suspends, then its result is returned directly,
 * otherwise it returns [COROUTINE_SUSPENDED] and the [completion] continuation is invoked when coroutine completes.
 */
@Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN", "UNCHECKED_CAST")
public fun <T> (suspend  () -> T).startCoroutineOrReturn(completion: Continuation<T>): Any? =
    (this as kotlin.jvm.functions.Function1<Continuation<T>, Any?>).invoke(completion)
