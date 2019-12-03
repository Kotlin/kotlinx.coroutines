package kotlinx.coroutines

import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext

internal actual fun createInitialContext(): CoroutineContext {
    return EmptyCoroutineContext
}
