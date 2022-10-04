/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")

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
    /**
     * The default [CoroutineDispatcher] that is used by all standard builders like
     * [launch][CoroutineScope.launch], [async][CoroutineScope.async], etc.
     * if no dispatcher nor any other [ContinuationInterceptor] is specified in their context.
     *
     * It is backed by a shared pool of threads on JVM. By default, the maximal level of parallelism used
     * by this dispatcher is equal to the number of CPU cores, but is at least two.
     * Level of parallelism X guarantees that no more than X tasks can be executed in this dispatcher in parallel.
     */
    @JvmStatic
    public actual val Default: CoroutineDispatcher = DefaultScheduler

    /**
     * A coroutine dispatcher that is confined to the Main thread operating with UI objects.
     * This dispatcher can be used either directly or via [MainScope] factory.
     * Usually such dispatcher is single-threaded.
     *
     * Access to this property may throw [IllegalStateException] if no main thread dispatchers are present in the classpath.
     *
     * Depending on platform and classpath it can be mapped to different dispatchers:
     * - On JS and Native it is equivalent of [Default] dispatcher.
     * - On JVM it is either Android main thread dispatcher, JavaFx or Swing EDT dispatcher. It is chosen by
     *   [`ServiceLoader`](https://docs.oracle.com/javase/8/docs/api/java/util/ServiceLoader.html).
     *
     * In order to work with `Main` dispatcher, the following artifacts should be added to project runtime dependencies:
     *  - `kotlinx-coroutines-android` for Android Main thread dispatcher
     *  - `kotlinx-coroutines-javafx` for JavaFx Application thread dispatcher
     *  - `kotlinx-coroutines-swing` for Swing EDT dispatcher
     *
     * In order to set a custom `Main` dispatcher for testing purposes, add the `kotlinx-coroutines-test` artifact to 
     * project test dependencies.
     *
     * Implementation note: [MainCoroutineDispatcher.immediate] is not supported on Native and JS platforms.
     */
    @JvmStatic
    public actual val Main: MainCoroutineDispatcher get() = MainDispatcherLoader.dispatcher

    /**
     * A coroutine dispatcher that is not confined to any specific thread.
     * It executes initial continuation of the coroutine in the current call-frame
     * and lets the coroutine resume in whatever thread that is used by the corresponding suspending function, without
     * mandating any specific threading policy. Nested coroutines launched in this dispatcher form an event-loop to avoid
     * stack overflows.
     *
     * ### Event loop
     * Event loop semantics is a purely internal concept and have no guarantees on the order of execution
     * except that all queued coroutines will be executed on the current thread in the lexical scope of the outermost
     * unconfined coroutine.
     *
     * For example, the following code:
     * ```
     * withContext(Dispatchers.Unconfined) {
     *    println(1)
     *    withContext(Dispatchers.Unconfined) { // Nested unconfined
     *        println(2)
     *    }
     *    println(3)
     * }
     * println("Done")
     * ```
     * Can print both "1 2 3" and "1 3 2", this is an implementation detail that can be changed.
     * But it is guaranteed that "Done" will be printed only when both `withContext` are completed.
     *
     *
     * Note that if you need your coroutine to be confined to a particular thread or a thread-pool after resumption,
     * but still want to execute it in the current call-frame until its first suspension, then you can use
     * an optional [CoroutineStart] parameter in coroutine builders like
     * [launch][CoroutineScope.launch] and [async][CoroutineScope.async] setting it to
     * the value of [CoroutineStart.UNDISPATCHED].
     */
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
