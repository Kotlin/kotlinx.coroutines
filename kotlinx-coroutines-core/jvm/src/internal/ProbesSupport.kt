@file:Suppress("NOTHING_TO_INLINE", "INVISIBLE_REFERENCE", "INVISIBLE_MEMBER")

package kotlinx.coroutines.internal

import kotlin.coroutines.*

internal actual inline fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> =
    kotlin.coroutines.jvm.internal.probeCoroutineCreated(completion)

internal actual inline fun <T> probeCoroutineResumed(completion: Continuation<T>) {
    kotlin.coroutines.jvm.internal.probeCoroutineResumed(completion)
}
