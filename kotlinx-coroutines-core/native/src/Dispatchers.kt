package kotlinx.coroutines

import kotlinx.coroutines.scheduling.DefaultIoScheduler


public actual object Dispatchers {
    public actual val Default: CoroutineDispatcher = createDefaultDispatcher()
    public actual val Main: MainCoroutineDispatcher
        get() = injectedMainDispatcher ?: mainDispatcher
    public actual val Unconfined: CoroutineDispatcher get() = kotlinx.coroutines.Unconfined // Avoid freezing

    private val mainDispatcher = createMainDispatcher(Default)

    private var injectedMainDispatcher: MainCoroutineDispatcher? = null

    @PublishedApi
    internal fun injectMain(dispatcher: MainCoroutineDispatcher) {
        injectedMainDispatcher = dispatcher
    }

    internal val IO: CoroutineDispatcher = DefaultIoScheduler
}

@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
public actual val Dispatchers.IO: CoroutineDispatcher get() = IO

internal expect fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher
