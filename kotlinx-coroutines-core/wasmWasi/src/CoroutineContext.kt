package kotlinx.coroutines

internal actual fun createDefaultDispatcher(): CoroutineDispatcher = WasiDispatcher
