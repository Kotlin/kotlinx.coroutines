package kotlinx.coroutines.internal

import kotlin.coroutines.*

internal expect fun threadContextElements(context: CoroutineContext): Any
