package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.CoroutineContext

public expect interface CoroutineScope {
    public val isActive: Boolean
    public val coroutineContext: CoroutineContext
}