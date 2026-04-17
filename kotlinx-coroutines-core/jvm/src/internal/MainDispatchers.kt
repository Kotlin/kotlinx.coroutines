package kotlinx.coroutines.internal

import kotlinx.coroutines.*
import java.util.*

/**
 * Name of the boolean property that enables using of [FastServiceLoader].
 */
private const val FAST_SERVICE_LOADER_PROPERTY_NAME = "kotlinx.coroutines.fast.service.loader"

// Lazy loader for the main dispatcher
internal object MainDispatcherLoader {

    private val FAST_SERVICE_LOADER_ENABLED = systemProp(FAST_SERVICE_LOADER_PROPERTY_NAME, true)

    @JvmField
    val dispatcherLoadResult = loadMainDispatcher()

    private fun loadMainDispatcher(): MainDispatcherLoadResult {
        val factories: List<MainDispatcherFactory>
        val preferredFactory = try {
            factories = if (FAST_SERVICE_LOADER_ENABLED) {
                FastServiceLoader.loadMainDispatcherFactory()
            } else {
                // We are explicitly using the
                // `ServiceLoader.load(MyClass::class.java, MyClass::class.java.classLoader).iterator()`
                // form of the ServiceLoader call to enable R8 optimization when compiled on Android.
                ServiceLoader.load(
                    MainDispatcherFactory::class.java,
                    MainDispatcherFactory::class.java.classLoader
                ).iterator().asSequence().toList()
            }
            /* Since `loadPriority` is also user-supplied and can fail, we have to keep it in this `try`. */
            factories.maxByOrNull { it.loadPriority }
        } catch (e: Throwable) {
            // Service loading failed for some internal, unpredictable reason.
            // The best we can do is to propagate the exception, mentioning broadly that it's Dispatchers.Main-related.
            return MainDispatcherLoadResult(null, null, e)
        }
        if (preferredFactory == null) {
            return MainDispatcherLoadResult(
                null,
                "Module with the Main dispatcher is missing. " +
                "Add a dependency providing the Main dispatcher, such as 'kotlinx-coroutines-android' " +
                "and ensure it has the same version as 'kotlinx-coroutines-core'",
                null
            )
        }
        val dispatcher = try {
            preferredFactory.createDispatcher(factories)
        } catch (cause: Throwable) {
            val message = buildString {
                append("Module with the Main dispatcher failed to initialize")
                preferredFactory.hintOnError()?.let {
                    append(". ")
                    append(it)
                }
            }
            return MainDispatcherLoadResult(null, message, cause)
        }
        return MainDispatcherLoadResult(dispatcher, null, null)
    }
}

internal class MainDispatcherLoadResult(
    val dispatcherOrNull: MainCoroutineDispatcher?,
    val failureMessageOrNull: String?,
    val failureCauseOrNull: Throwable?
)
