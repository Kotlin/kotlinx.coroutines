/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmName("SystemPropsKt")
@file:JvmMultifileClass

package kotlinx.coroutines.internal

import kotlin.jvm.*

/**
 * Gets the system property indicated by the specified [property name][propertyName],
 * or returns [defaultValue] if there is no property with that key.
 *
 * **Note: this function should be used in JVM tests only, other platforms use the default value.**
 */
internal fun systemProp(
    propertyName: String,
    defaultValue: Boolean
): Boolean = systemProp(propertyName)?.toBoolean() ?: defaultValue

/**
 * Gets the system property indicated by the specified [property name][propertyName],
 * or returns [defaultValue] if there is no property with that key. It also checks that the result
 * is between [minValue] and [maxValue] (inclusively), throws [IllegalStateException] if it is not.
 *
 * **Note: this function should be used in JVM tests only, other platforms use the default value.**
 */
internal fun systemProp(
    propertyName: String,
    defaultValue: Int,
    minValue: Int = 1,
    maxValue: Int = Int.MAX_VALUE
): Int = systemProp(propertyName, defaultValue.toLong(), minValue.toLong(), maxValue.toLong()).toInt()

/**
 * Gets the system property indicated by the specified [property name][propertyName],
 * or returns [defaultValue] if there is no property with that key. It also checks that the result
 * is between [minValue] and [maxValue] (inclusively), throws [IllegalStateException] if it is not.
 *
 * **Note: this function should be used in JVM tests only, other platforms use the default value.**
 */
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

/**
 * Gets the system property indicated by the specified [property name][propertyName],
 * or returns `null` if there is no property with that key.
 *
 * **Note: this function should be used in JVM tests only, other platforms use the default value.**
 */
internal expect fun systemProp(propertyName: String): String?
