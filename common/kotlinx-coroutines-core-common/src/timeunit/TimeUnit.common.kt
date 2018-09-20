/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.timeunit

/*
 * @suppress **Deprecated** No replacement
 */
@Suppress("ACTUAL_WITHOUT_EXPECT")
@Deprecated(message = "No replacement")
public expect enum class TimeUnit {
    MILLISECONDS,
    SECONDS;

    public fun toMillis(time: Long): Long
}