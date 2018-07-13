/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */
package kotlinx.coroutines.timeunit

public actual enum class TimeUnit {
    MILLISECONDS,
    SECONDS;

    public actual fun toMillis(time: Long): Long = when(this) {
        MILLISECONDS -> time
        SECONDS -> when {
            time >= Long.MAX_VALUE / 1000L -> Long.MAX_VALUE
            time <= Long.MIN_VALUE / 1000L -> Long.MIN_VALUE
            else -> time * 1000L
        }
    }

    public fun toNanos(time: Long): Long = when(this) {
        MILLISECONDS -> when {
            time >= Long.MAX_VALUE / 1000_000L -> Long.MAX_VALUE
            time <= Long.MIN_VALUE / 1000_000L -> Long.MIN_VALUE
            else -> time * 1000_000L
        }
        SECONDS -> when {
            time >= Long.MAX_VALUE / 1000_000_000L -> Long.MAX_VALUE
            time <= Long.MIN_VALUE / 1000_000_000L -> Long.MIN_VALUE
            else -> time * 1000_000_000L
        }
    }
}
