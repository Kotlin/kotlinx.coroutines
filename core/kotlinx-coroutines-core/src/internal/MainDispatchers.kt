package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import java.util.*
import kotlin.coroutines.*

// Lazy loader for the main dispatcher
internal object MainDispatcherLoader {
    @JvmField
    val dispatcher: MainCoroutineDispatcher = loadMainDispatcher()

    private fun loadMainDispatcher(): MainCoroutineDispatcher {
        return try {
            val factories = MainDispatcherFactory::class.java.let { clz ->
                ServiceLoader.load(clz, clz.classLoader).toList()
            }

            factories.maxBy { it.loadPriority }?.tryCreateDispatcher(factories)
                ?: MissingMainCoroutineDispatcher(null)
        } catch (e: Throwable) {
            // Catch any initialization errors or ServiceConfigurationError
            MissingMainCoroutineDispatcher(e)
        }
    }
}

/**
 * If anything goes wrong while trying to create main dispatcher (class not found,
 * initialization failed, etc), then replace the main dispatcher with a special
 * stub that throws an error message on any attempt to actually use it.
 */
@InternalCoroutinesApi
public fun MainDispatcherFactory.tryCreateDispatcher(factories: List<MainDispatcherFactory>): MainCoroutineDispatcher =
    try {
        createDispatcher(factories)
    } catch (cause: Throwable) {
        MissingMainCoroutineDispatcher(cause)
    }

private class MissingMainCoroutineDispatcher(val cause: Throwable?) : MainCoroutineDispatcher(), Delay {
    override val immediate: MainCoroutineDispatcher get() = this

    override fun dispatch(context: CoroutineContext, block: Runnable) =
        missing()

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) =
        missing()

    private fun missing() {
        if  (cause == null) {
            throw IllegalStateException(
                "Module with the Main dispatcher is missing. " +
                        "Add dependency providing the Main dispatcher, e.g. 'kotlinx-coroutines-android'"
            )
        } else {
            throw IllegalStateException("Module with the Main dispatcher had failed to initialize", cause)
        }
    }

    override fun toString(): String = "Main[missing${if (cause != null) ", cause=$cause" else ""}]"
}

@InternalCoroutinesApi
public object MissingMainCoroutineDispatcherFactory : MainDispatcherFactory {
    override val loadPriority: Int
        get() = -1

    override fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher {
       return MissingMainCoroutineDispatcher(null)
    }
}
