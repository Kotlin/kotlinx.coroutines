/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines


public actual object Dispatchers {
    public actual val Default: CoroutineDispatcher = createDefaultDispatcher()
    public actual val Main: MainCoroutineDispatcher
        get() = injectedMainDispatcher ?: mainDispatcher
    public actual val Unconfined: CoroutineDispatcher get() = kotlinx.coroutines.Unconfined // Avoid freezing

    private val mainDispatcher = createMainDispatcher(Default)

    private var injectedMainDispatcher: MainCoroutineDispatcher? = null

    @PublishedApi
    internal fun injectMain(dispatcher: MainCoroutineDispatcher) {
        injectedMainDispatcher = dispatcher
    }

    internal val IO: CoroutineDispatcher = newFixedThreadPoolContext(64, "Dispatchers.IO")
}

/**
 * The [CoroutineDispatcher] that is designed for offloading blocking IO tasks to a shared pool of threads.
 * Additional threads in this pool are created on demand.
 *
 * On Native platforms it is backed by a standalone [newFixedThreadPoolContext] with `64` worker threads in it.
 * **NB**: this dispatcher **does not** share the same elasticity behaviour for [CoroutineDispatcher.limitedParallelism]
 * as `Dispatchers.IO` on JVM.
 */
@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
public actual val Dispatchers.IO: CoroutineDispatcher get() = IO

internal expect fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher
