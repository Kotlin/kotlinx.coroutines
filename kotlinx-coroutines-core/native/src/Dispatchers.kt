package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlin.coroutines.*


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

internal object DefaultIoScheduler : CoroutineDispatcher() {
    // 2048 is an arbitrary KMP-friendly constant
    private val unlimitedPool = newFixedThreadPoolContext(2048, "Dispatchers.IO")
    private val io = unlimitedPool.limitedParallelism(64) // Default JVM size

    override fun limitedParallelism(parallelism: Int, name: String?): CoroutineDispatcher {
        // See documentation to Dispatchers.IO for the rationale
        return unlimitedPool.limitedParallelism(parallelism, name)
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        io.dispatch(context, block)
    }

    @InternalCoroutinesApi
    override fun dispatchYield(context: CoroutineContext, block: Runnable) {
        io.dispatchYield(context, block)
    }

    override fun toString(): String = "Dispatchers.IO"
}


@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
public actual val Dispatchers.IO: CoroutineDispatcher get() = IO

internal expect fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher
