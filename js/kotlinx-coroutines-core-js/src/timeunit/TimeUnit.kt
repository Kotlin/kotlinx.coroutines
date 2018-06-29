/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.timeunit

/**
 * Time unit. This class is provided for better JVM interoperability.
 * **It is available for common code, but its use in common code is not recommended.**
 */
@Deprecated("Using this TimeUnit enum in JS code is not recommended, use functions without it")
public actual enum class TimeUnit {
    /** Milliseconds. */
    MILLISECONDS,
    /** Seconds. */
    SECONDS;

    /**
     * Converts time in this time unit to milliseconds.
     */
    public actual fun toMillis(time: Long): Long = when(this) {
        MILLISECONDS -> time
        SECONDS -> when {
            time >= Long.MAX_VALUE / 1000L -> Long.MAX_VALUE
            time <= Long.MIN_VALUE / 1000L -> Long.MIN_VALUE
            else -> time * 1000L
        }
    }
}