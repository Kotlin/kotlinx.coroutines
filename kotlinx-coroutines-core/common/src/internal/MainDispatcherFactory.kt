/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*

/** @suppress */
@InternalCoroutinesApi // Emulating DI for Kotlin object's
public interface MainDispatcherFactory {
    public val loadPriority: Int // higher priority wins

    /**
     * Creates the main dispatcher. [allFactories] parameter contains all factories found by service loader.
     * This method is not guaranteed to be idempotent.
     */
    public fun createDispatcher(allFactories: List<MainDispatcherFactory>): MainCoroutineDispatcher

    /**
     * Hint used along with error message when the factory failed to create a dispatcher.
     */
    public fun hintOnError(): String? = null
}
