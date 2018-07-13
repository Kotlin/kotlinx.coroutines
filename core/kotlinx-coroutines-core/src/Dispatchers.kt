/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import kotlinx.coroutines.scheduling.*
import java.util.*

/**
 * Name of the property that defines the maximal number of threads that are used by [Dispatchers.IO] coroutines dispatcher.
 */
public const val IO_PARALLELISM_PROPERTY_NAME = "kotlinx.coroutines.io.parallelism"

/**
 * Groups various implementations of [CoroutineDispatcher].
 */
public actual object Dispatchers {

    /**
     * The default [CoroutineDispatcher] that is used by all standard builders like
     * [launch][CoroutineScope.launch], [async][CoroutineScope.async], etc
     * if no dispatcher nor any other [ContinuationInterceptor] is specified in their context.
     *
     * It is backed by a shared pool of threads on JVM. By default, the maximal number of threads used
     * by this dispatcher is equal to the number CPU cores, but is at least two.
     */
    @JvmStatic
    public actual val Default: CoroutineDispatcher = createDefaultDispatcher()

    /**
     * A coroutine dispatcher that is confined to the Main thread operating with UI objects.
     * Usually such dispatcher is single-threaded.
     *
     * Access to this property may throw [IllegalStateException] if no main thread dispatchers are present in the classpath.
     *
     * Depending on platform and classpath it can be mapped to different dispatchers:
     * - On JS and Native it is equivalent of [Default] dispatcher.
     * - On JVM it either Android main thread dispatcher, JavaFx or Swing EDT dispatcher. It is chosen by
     *   [`ServiceLoader`](https://docs.oracle.com/javase/8/docs/api/java/util/ServiceLoader.html).
     *
     * In order to work with `Main` dispatcher, following artifact should be added to project runtime dependencies:
     *  - `kotlinx-coroutines-android` for Android Main thread dispatcher
     *  - `kotlinx-coroutines-javafx` for JavaFx Application thread dispatcher
     *  - `kotlinx-coroutines-swing` for Swing EDT dispatcher
     *
     * Implementation note: [MainCoroutineDispatcher.immediate] is not supported on Native and JS platforms.
     */
    @JvmStatic
    public actual val Main: MainCoroutineDispatcher get() = MainDispatcherLoader.dispatcher

    /**
     * A coroutine dispatcher that is not confined to any specific thread.
     * It executes initial continuation of the coroutine _immediately_ in the current call-frame
     * and lets the coroutine resume in whatever thread that is used by the corresponding suspending function, without
     * mandating any specific threading policy.
     * **Note: use with extreme caution, not for general code**.
     *
     * Note, that if you need your coroutine to be confined to a particular thread or a thread-pool after resumption,
     * but still want to execute it in the current call-frame until its first suspension, then you can use
     * an optional [CoroutineStart] parameter in coroutine builders like
     * [launch][CoroutineScope.launch] and [async][CoroutineScope.async] setting it to the
     * the value of [CoroutineStart.UNDISPATCHED].
     *
     * **Note: This is an experimental api.**
     * Semantics, order of execution, and particular implementation details of this dispatcher may change in the future.
     */
    @JvmStatic
    @ExperimentalCoroutinesApi
    public actual val Unconfined: CoroutineDispatcher = kotlinx.coroutines.Unconfined

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
    @JvmStatic
    public val IO: CoroutineDispatcher = DefaultScheduler.IO
}

// Lazy loader for the main dispatcher
private object MainDispatcherLoader {
    @JvmField
    val dispatcher: MainCoroutineDispatcher =
        MainDispatcherFactory::class.java.let { clz ->
            ServiceLoader.load(clz, clz.classLoader).toList()
        }.maxBy { it.loadPriority }?.tryCreateDispatcher() ?: MissingMainCoroutineDispatcher(null)

    /**
     * If anything goes wrong while trying to create main dispatcher (class not found,
     * initialization failed, etc), then replace the main dispatcher with a special
     * stub that throws an error message on any attempt to actually use it.
     */
    private fun MainDispatcherFactory.tryCreateDispatcher(): MainCoroutineDispatcher =
        try {
            createDispatcher()
        } catch (cause: Throwable) {
            MissingMainCoroutineDispatcher(cause)
        }
}

private class MissingMainCoroutineDispatcher(val cause: Throwable?) : MainCoroutineDispatcher(), Delay {
    override val immediate: MainCoroutineDispatcher get() = this

    override fun dispatch(context: CoroutineContext, block: Runnable) =
        missing()

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) =
        missing()

    private fun missing() {
        if  (cause == null) {
            throw IllegalStateException(
                "Module with the Main dispatcher is missing. " +
                    "Add dependency providing the Main dispatcher, e.g. 'kotlinx-coroutines-android'"
            )
        } else {
            throw IllegalStateException("Module with the Main dispatcher had failed to initialize", cause)
        }
    }

    override fun toString(): String = "Main[missing${if (cause != null) ", cause=$cause" else ""}]"
}