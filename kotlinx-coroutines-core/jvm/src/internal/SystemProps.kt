@file:JvmName("SystemPropsKt")
@file:JvmMultifileClass

package kotlinx.coroutines.internal

internal actual fun systemProp(
    propertyName: String
): String? =
    try {
        System.getProperty(propertyName)
    } catch (e: SecurityException) {
        null
    }
