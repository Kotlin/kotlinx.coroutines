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
package kotlinx.coroutines.experimental.time

import kotlinx.coroutines.experimental.selects.SelectBuilder
import java.time.Duration
import java.util.concurrent.TimeUnit

/**
 * "java.time" adapter method for [kotlinx.coroutines.experimental.delay]
 */
public suspend fun delay(duration: Duration) =
        kotlinx.coroutines.experimental.delay(duration.toNanos(), TimeUnit.NANOSECONDS)

/**
 * "java.time" adapter method for [SelectBuilder.onTimeout]
 */
public suspend fun <R> SelectBuilder<R>.onTimeout(duration: Duration, block: suspend () -> R) =
        onTimeout(duration.toNanos(), TimeUnit.NANOSECONDS, block)

/**
 * "java.time" adapter method for [kotlinx.coroutines.experimental.withTimeout]
 */
public suspend fun <T> withTimeout(duration: Duration, block: suspend () -> T): T =
        kotlinx.coroutines.experimental.withTimeout(duration.toNanos(), TimeUnit.NANOSECONDS, block)

/**
 * "java.time" adapter method for [kotlinx.coroutines.experimental.withTimeoutOrNull]
 */
public suspend fun <T> withTimeoutOrNull(duration: Duration, block: suspend () -> T): T? =
        kotlinx.coroutines.experimental.withTimeoutOrNull(duration.toNanos(), TimeUnit.NANOSECONDS, block)
