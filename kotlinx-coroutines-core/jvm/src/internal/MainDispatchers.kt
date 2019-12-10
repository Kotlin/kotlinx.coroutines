package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import java.util.*
import kotlin.coroutines.*

/**
 * Name of the boolean property that enables using of [FastServiceLoader].
 */
private const val FAST_SERVICE_LOADER_PROPERTY_NAME = "kotlinx.coroutines.fast.service.loader"

// Lazy loader for the main dispatcher
internal object MainDispatcherLoader {

    private val FAST_SERVICE_LOADER_ENABLED = systemProp(FAST_SERVICE_LOADER_PROPERTY_NAME, true)

    @JvmField
    val dispatcher: MainCoroutineDispatcher = loadMainDispatcher()

    private fun loadMainDispatcher(): MainCoroutineDispatcher {
        return try {
            val factories = if (FAST_SERVICE_LOADER_ENABLED) {
                MainDispatcherFactory::class.java.let { clz ->
                    FastServiceLoader.load(clz, clz.classLoader)
                }
            } else {
                //We are explicitly using the
                //`ServiceLoader.load(MyClass::class.java, MyClass::class.java.classLoader).iterator()`
                //form of the ServiceLoader call to enable R8 optimization when compiled on Android.
                ServiceLoader.load(
                        MainDispatcherFactory::class.java,
                        MainDispatcherFactory::class.java.classLoader
                ).iterator().asSequence().toList()
            }
            factories.maxBy { it.loadPriority }?.tryCreateDispatcher(factories)
                ?: MissingMainCoroutineDispatcher(null)
        } catch (e: Throwable) {
            // Service loader can throw an exception as well
            MissingMainCoroutineDispatcher(e)
        }
    }
}

/**
 * If anything goes wrong while trying to create main dispatcher (class not found,
 * initialization failed, etc), then replace the main dispatcher with a special
 * stub that throws an error message on any attempt to actually use it.
 *
 * @suppress internal API
 */
@InternalCoroutinesApi
public fun MainDispatcherFactory.tryCreateDispatcher(factories: List<MainDispatcherFactory>): MainCoroutineDispatcher =
    try {
        createDispatcher(factories)
    } catch (cause: Throwable) {
        MissingMainCoroutineDispatcher(cause, hintOnError())
    }

/** @suppress */
@InternalCoroutinesApi
public fun MainCoroutineDispatcher.isMissing(): Boolean = this is MissingMainCoroutineDispatcher

private class MissingMainCoroutineDispatcher(
    private val cause: Throwable?,
    private val errorHint: String? = null
) : MainCoroutineDispatcher(), Delay {

    override val immediate: MainCoroutineDispatcher get() = this

    override fun isDispatchNeeded(context: CoroutineContext): Boolean {
        missing()
    }

    override suspend fun delay(time: Long) {
        missing()
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        missing()
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) =
        missing()

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) =
        missing()

    private fun missing(): Nothing {
        if  (cause == null) {
            throw IllegalStateException(
                "Module with the Main dispatcher is missing. " +
                    "Add dependency providing the Main dispatcher, e.g. 'kotlinx-coroutines-android' " +
                        "and ensure it has the same version as 'kotlinx-coroutines-core'"
            )
        } else {
            val message = "Module with the Main dispatcher had failed to initialize" + (errorHint?.let { ". $it" } ?: "")
            throw IllegalStateException(message, cause)
        }
    }

    override fun toString(): String = "Main[missing${if (cause != null) ", cause=$cause" else ""}]"
}

/**
 * @suppress
 */
@InternalCoroutinesApi
public object MissingMainCoroutineDispatcherFactory : MainDispatcherFactory {
    override val loadPriority: Int
        get() = -1

    override fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher {
        return MissingMainCoroutineDispatcher(null)
    }
}