/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*


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

    public actual val IO: CoroutineDispatcher = DefaultIoScheduler
}

internal object DefaultIoScheduler : CoroutineDispatcher() {
    // 2048 is an arbitrary KMP-friendly constant
    private val unlimitedPool = newFixedThreadPoolContext(2048, "Dispatchers.IO")
    private val io = unlimitedPool.limitedParallelism(64) // Default JVM size

    @ExperimentalCoroutinesApi
    override fun limitedParallelism(parallelism: Int): CoroutineDispatcher {
        // See documentation to Dispatchers.IO for the rationale
        return unlimitedPool.limitedParallelism(parallelism)
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        io.dispatch(context, block)
    }

    @InternalCoroutinesApi
    override fun dispatchYield(context: CoroutineContext, block: Runnable) {
        io.dispatchYield(context, block)
    }

    override fun toString(): String = "Dispatchers.IO"
}

/**
 * Should never be used directly from native sources, all accesses
 * to `Dispatchers.IO` should be resolved to the corresponding member of [Dispatchers] object.
 * Saved for binary compatibility.
 * @suppress
 */
@Suppress("EXTENSION_SHADOWED_BY_MEMBER")
@Deprecated("May be removed in the future releases")
public val Dispatchers.IO: CoroutineDispatcher get() = IO

internal expect fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher
