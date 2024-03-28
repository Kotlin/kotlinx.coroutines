package kotlinx.coroutines.internal

import kotlin.coroutines.*

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T> = completion

@Suppress("NOTHING_TO_INLINE")
internal actual inline fun <T> probeCoroutineResumed(completion: Continuation<T>) { }
