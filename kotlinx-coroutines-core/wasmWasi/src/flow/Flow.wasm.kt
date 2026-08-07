package kotlinx.coroutines.flow

public actual interface Flow<out T> {
    public actual suspend fun collect(collector: FlowCollector<T>)
}
