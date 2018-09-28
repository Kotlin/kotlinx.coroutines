/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")

package kotlinx.coroutines.experimental

import kotlinx.coroutines.experimental.scheduling.*

/**
 * Name of the property that defines the maximal number of threads that are used by [Dispatchers.IO] coroutines dispatcher.
 */
public const val IO_PARALLELISM_PROPERTY_NAME = "kotlinx.coroutines.io.parallelism"

/**
 * The [CoroutineDispatcher] that is designed for offloading blocking IO tasks to a shared pool of threads.
 *
 * Additional threads in this pool are created and are shutdown on demand.
 * The number of threads used by this dispatcher is limited by the value of
 * "`kotlinx.coroutines.io.parallelism`" ([IO_PARALLELISM_PROPERTY_NAME]) system property.
 * It defaults to the limit of 64 threads or the number of cores (whichever is larger).
 *
 * This dispatcher shares threads with a [Default][Dispatchers.Default] dispatcher, so using
 * `withContext(Dispatchers.IO) { ... }` does not lead to an actual switching to another thread &mdash;
 * typically execution continues in the same thread.
 */
public val Dispatchers.IO: CoroutineDispatcher
    get() = DefaultScheduler.IO
