package kotlinx.coroutines.internal

import kotlin.coroutines.*

internal expect inline fun <T> probeCoroutineCreated(completion: Continuation<T>): Continuation<T>
