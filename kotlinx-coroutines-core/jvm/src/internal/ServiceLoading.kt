package kotlinx.coroutines.internal

import java.util.*

/**
 * Name of the boolean property that enables using of [FastServiceLoader].
 */
private const val FAST_SERVICE_LOADER_PROPERTY_NAME = "kotlinx.coroutines.fast.service.loader"

private val FAST_SERVICE_LOADER_ENABLED = systemProp(FAST_SERVICE_LOADER_PROPERTY_NAME, true)

/**
 * Load all services of specified type via Java's [ServiceLoader] or [FastServiceLoader],
 * depending on the value of [FAST_SERVICE_LOADER_ENABLED] system property.
 */
internal inline fun <reified T> loadServices(): List<T> {
    return if (FAST_SERVICE_LOADER_ENABLED) {
        T::class.java.let { clz ->
            FastServiceLoader.load(clz, clz.classLoader)
        }
    } else {
        // We are explicitly using the
        // `ServiceLoader.load(MyClass::class.java, MyClass::class.java.classLoader).iterator()`
        // form of the ServiceLoader call to enable R8 optimization when compiled on Android.
        ServiceLoader.load(T::class.java, T::class.java.classLoader).iterator().asSequence().toList()
    }
}

