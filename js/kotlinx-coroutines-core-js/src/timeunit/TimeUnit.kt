/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
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