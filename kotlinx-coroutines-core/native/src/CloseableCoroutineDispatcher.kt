package kotlinx.coroutines

@OptIn(ExperimentalSubclassOptIn::class)
public actual abstract class CloseableCoroutineDispatcher actual constructor() : CoroutineDispatcher(), AutoCloseable {
    public actual abstract override fun close()
}
