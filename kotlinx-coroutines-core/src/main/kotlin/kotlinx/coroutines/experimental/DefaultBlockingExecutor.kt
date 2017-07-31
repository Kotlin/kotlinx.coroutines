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

package kotlinx.coroutines.experimental

import java.util.concurrent.*

private const val DEFAULT_CORE_POOL_SIZE = 1
private const val DEFAULT_KEEP_ALIVE = 60_000L // in milliseconds
private const val DEFAULT_MAXIMUM_POOL_SIZE = 256

private val KEEP_ALIVE = try {
    java.lang.Long.getLong("kotlinx.coroutines.DefaultBlockingExecutor.keepAlive", DEFAULT_KEEP_ALIVE)
} catch (e: SecurityException) {
    DEFAULT_KEEP_ALIVE
}

private val MAXIMUM_POOL_SIZE = try {
    java.lang.Integer.getInteger("kotlinx.coroutines.DefaultBlockingExecutor.maximumPoolSize", DEFAULT_MAXIMUM_POOL_SIZE)
} catch (e: SecurityException) {
    DEFAULT_MAXIMUM_POOL_SIZE
}

internal object DefaultBlockingExecutor : Executor by ThreadPoolExecutor(
        DEFAULT_CORE_POOL_SIZE,
        MAXIMUM_POOL_SIZE,
        KEEP_ALIVE, TimeUnit.MILLISECONDS,
        LinkedBlockingQueue<Runnable>(),
        ThreadFactory { Thread(it, "kotlinx.coroutines.DefaultBlockingExecutor").apply { isDaemon = true } }
)
