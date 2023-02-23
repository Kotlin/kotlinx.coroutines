/*
 * Copyright 2016-2023 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.scheduling.*
import kotlin.coroutines.*

/**
 * Name of the property that defines the maximal number of threads that are used by [Dispatchers.IO] coroutines dispatcher.
 */
public const val IO_PARALLELISM_PROPERTY_NAME: String = "kotlinx.coroutines.io.parallelism"

/**
 * Groups various implementations of [CoroutineDispatcher].
 */
public actual object Dispatchers {
    @JvmStatic
    public actual val Default: CoroutineDispatcher = DefaultScheduler

    @JvmStatic
    public actual val Main: MainCoroutineDispatcher get() = MainDispatcherLoader.dispatcher

    @JvmStatic
    public actual val Unconfined: CoroutineDispatcher = kotlinx.coroutines.Unconfined

    /**
     * The [CoroutineDispatcher] that is designed for offloading blocking IO tasks to a shared pool of threads.
     *
     * Additional threads in this pool are created and are shutdown on demand.
     * The number of threads used by tasks in this dispatcher is limited by the value of
     * "`kotlinx.coroutines.io.parallelism`" ([IO_PARALLELISM_PROPERTY_NAME]) system property.
     * It defaults to the limit of 64 threads or the number of cores (whichever is larger).
     *
     * ### Elasticity for limited parallelism
     *
     * `Dispatchers.IO` has a unique property of elasticity: its views
     * obtained with [CoroutineDispatcher.limitedParallelism] are
     * not restricted by the `Dispatchers.IO` parallelism. Conceptually, there is
     * a dispatcher backed by an unlimited pool of threads, and both `Dispatchers.IO`
     * and views of `Dispatchers.IO` are actually views of that dispatcher. In practice
     * this means that, despite not abiding by `Dispatchers.IO`'s parallelism
     * restrictions, its views share threads and resources with it.
     *
     * In the following example
     * ```
     * // 100 threads for MySQL connection
     * val myMysqlDbDispatcher = Dispatchers.IO.limitedParallelism(100)
     * // 60 threads for MongoDB connection
     * val myMongoDbDispatcher = Dispatchers.IO.limitedParallelism(60)
     * ```
     * the system may have up to `64 + 100 + 60` threads dedicated to blocking tasks during peak loads,
     * but during its steady state there is only a small number of threads shared
     * among `Dispatchers.IO`, `myMysqlDbDispatcher` and `myMongoDbDispatcher`.
     *
     * ### Implementation note
     *
     * This dispatcher and its views share threads with the [Default][Dispatchers.Default] dispatcher, so using
     * `withContext(Dispatchers.IO) { ... }` when already running on the [Default][Dispatchers.Default]
     * dispatcher typically does not lead to an actual switching to another thread. In such scenarios,
     * the underlying implementation attempts to keep the execution on the same thread on a best-effort basis.
     *
     * As a result of thread sharing, more than 64 (default parallelism) threads can be created (but not used)
     * during operations over IO dispatcher.
     */
    @JvmStatic
    public val IO: CoroutineDispatcher = DefaultIoScheduler

    /**
     * Shuts down built-in dispatchers, such as [Default] and [IO],
     * stopping all the threads associated with them and making them reject all new tasks.
     * Dispatcher used as a fallback for time-related operations (`delay`, `withTimeout`)
     * and to handle rejected tasks from other dispatchers is also shut down.
     *
     * This is a **delicate** API. It is not supposed to be called from a general
     * application-level code and its invocation is irreversible.
     * The invocation of shutdown affects most of the coroutines machinery and
     * leaves the coroutines framework in an inoperable state.
     * The shutdown method should only be invoked when there are no pending tasks or active coroutines.
     * Otherwise, the behavior is unspecified: the call to `shutdown` may throw an exception without completing
     * the shutdown, or it may finish successfully, but the remaining jobs will be in a permanent dormant state,
     * never completing nor executing.
     *
     * The main goal of the shutdown is to stop all background threads associated with the coroutines
     * framework in order to make kotlinx.coroutines classes unloadable by Java Virtual Machine.
     * It is only recommended to be used in containerized environments (OSGi, Gradle plugins system,
     * IDEA plugins) at the end of the container lifecycle.
     */
    @DelicateCoroutinesApi
    public fun shutdown() {
        DefaultExecutor.shutdown()
        // Also shuts down Dispatchers.IO
        DefaultScheduler.shutdown()
    }
}

/**
 * `actual` counterpart of the corresponding `expect` declaration.
 * Should never be used directly from JVM sources, all accesses
 * to `Dispatchers.IO` should be resolved to the corresponding member of [Dispatchers] object.
 * @suppress
 */
@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
@Deprecated(message = "Should not be used directly", level = DeprecationLevel.HIDDEN)
public actual val Dispatchers.IO: CoroutineDispatcher get() = Dispatchers.IO
