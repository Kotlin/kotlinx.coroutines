/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

/** Not inside [Dispatchers], as otherwise mutating this throws an `InvalidMutabilityException`. */
private var injectedMainDispatcher: MainCoroutineDispatcher? = null

public actual object Dispatchers {
    public actual val Default: CoroutineDispatcher = createDefaultDispatcher()
    public actual val Main: MainCoroutineDispatcher
        get() = injectedMainDispatcher ?: mainDispatcher
    public actual val Unconfined: CoroutineDispatcher get() = kotlinx.coroutines.Unconfined // Avoid freezing

    private val mainDispatcher = createMainDispatcher(Default)

    @PublishedApi
    internal fun injectMain(dispatcher: MainCoroutineDispatcher) {
        injectedMainDispatcher = dispatcher
    }

    @PublishedApi
    internal fun resetInjectedMain() {
        injectedMainDispatcher = null
    }
}
internal expect fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher

