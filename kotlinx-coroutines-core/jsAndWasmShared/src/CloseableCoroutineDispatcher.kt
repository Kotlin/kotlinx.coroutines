package kotlinx.coroutines

public actual abstract class CloseableCoroutineDispatcher actual constructor() : CoroutineDispatcher() {
    public actual abstract fun close()
}
