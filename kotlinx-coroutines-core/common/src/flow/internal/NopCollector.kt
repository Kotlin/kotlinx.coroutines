package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.flow.*

internal object NopCollector : FlowCollector<Any?> {
    override suspend fun emit(value: Any?) {
        // does nothing
    }
}
