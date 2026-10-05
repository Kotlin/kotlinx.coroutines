package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlin.coroutines.*

internal actual class SafeCollector<T> actual constructor(
    internal actual val collector: FlowCollector<T>,
    internal actual val collectContext: CoroutineContext
) : FlowCollector<T> {
    private var lastEmissionContext: CoroutineContext? = null

    actual override suspend fun emit(value: T) {
        val currentContext = currentCoroutineContext()
        currentContext.ensureActive()
        if (lastEmissionContext !== currentContext) {
            checkContext(currentContext)
            lastEmissionContext = currentContext
        }
        collector.emit(value)
    }

    public actual fun releaseIntercepted() {
    }
}
