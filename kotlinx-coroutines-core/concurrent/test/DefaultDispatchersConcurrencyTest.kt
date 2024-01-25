package kotlinx.coroutines

class DefaultDispatcherConcurrencyTest : AbstractDispatcherConcurrencyTest() {
    override val dispatcher: CoroutineDispatcher = Dispatchers.Default
}

class IoDispatcherConcurrencyTest : AbstractDispatcherConcurrencyTest() {
    override val dispatcher: CoroutineDispatcher = Dispatchers.IO
}
