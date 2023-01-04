/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

/**
 * The [CoroutineDispatcher] that is designed for offloading blocking IO tasks to a shared pool of threads.
 * Additional threads in this pool are created on demand.
 *
 * By default, the pool is backed by `64` standalone threads, for the additional details
 * such as elasticity, dynamic sizing and interaction with [CoroutineDispatcher.limitedParallelism],
 * please refer to the documentation of `Dispatchers.IO` on specific platform.
 */
@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
public expect val Dispatchers.IO: CoroutineDispatcher


