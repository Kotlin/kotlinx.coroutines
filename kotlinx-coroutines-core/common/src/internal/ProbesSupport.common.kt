package kotlinx.coroutines.internal

import kotlin.coroutines.*

internal expect inline fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T>

internal expect inline fun <T> probeCoroutineResumed(completion: Continuation<T>): Unit
