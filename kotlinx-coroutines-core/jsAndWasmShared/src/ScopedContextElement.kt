package kotlinx.coroutines

import kotlin.coroutines.*

public actual interface ScopedContextElement<S> : CoroutineContext.Element {
    public actual fun updateThreadContext(context: CoroutineContext): S
    public actual fun restoreThreadContext(context: CoroutineContext, oldState: S)
}
