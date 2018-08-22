/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

// number of processors at startup for consistent prop initialization
internal val AVAILABLE_PROCESSORS = Runtime.getRuntime().availableProcessors()

internal fun systemProp(
    propertyName: String
): String? =
    try {
        System.getProperty(propertyName)
    } catch (e: SecurityException) {
        null
    }

internal fun systemProp(
    propertyName: String,
    defaultValue: Boolean
): Boolean =
    try {
        System.getProperty(propertyName)?.toBoolean() ?: defaultValue
    } catch (e: SecurityException) {
        defaultValue
    }

internal fun systemProp(
    propertyName: String,
    defaultValue: Int,
    minValue: Int = 1,
    maxValue: Int = Int.MAX_VALUE
): Int
    = systemProp(propertyName, defaultValue.toLong(), minValue.toLong(), maxValue.toLong()).toInt()

internal fun systemProp(
    propertyName: String,
    defaultValue: Long,
    minValue: Long = 1,
    maxValue: Long = Long.MAX_VALUE
): Long {
    val value = systemProp(propertyName) ?: return defaultValue
    val parsed = value.toLongOrNull()
        ?: error("System property '$propertyName' has unrecognized value '$value'")
    if (parsed !in minValue..maxValue) {
        error("System property '$propertyName' should be in range $minValue..$maxValue, but is '$parsed'")
    }
    return parsed
}
