@file:JvmName("SystemPropsKt")
@file:JvmMultifileClass

package kotlinx.coroutines.internal

// number of processors at startup for consistent prop initialization
internal val AVAILABLE_PROCESSORS = Runtime.getRuntime().availableProcessors()

internal actual fun systemProp(
    propertyName: String
): String? =
    try {
        System.getProperty(propertyName)
    } catch (e: SecurityException) {
        null
    }
