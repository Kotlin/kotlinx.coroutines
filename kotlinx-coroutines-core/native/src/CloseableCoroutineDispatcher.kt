package kotlinx.coroutines

@SubclassOptInRequired(BrittleForInheritanceCoroutinesApi::class)
public actual abstract class CloseableCoroutineDispatcher actual constructor() : CoroutineDispatcher(), AutoCloseable {
    public actual abstract override fun close()
}
