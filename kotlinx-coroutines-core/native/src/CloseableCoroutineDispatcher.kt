package kotlinx.coroutines

@OptIn(ExperimentalSubclassOptIn::class)
@SubclassOptInRequired(ExperimentalForInheritanceCoroutinesApi::class)
public actual abstract class CloseableCoroutineDispatcher actual constructor() : CoroutineDispatcher(), AutoCloseable {
    public actual abstract override fun close()
}
