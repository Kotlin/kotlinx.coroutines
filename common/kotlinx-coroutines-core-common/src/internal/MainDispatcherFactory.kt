/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.internal

import kotlinx.coroutines.*

/** @suppress */
@InternalCoroutinesApi // Emulating DI for Kotlin object's
public interface MainDispatcherFactory {
    val loadPriority: Int // higher priority wins

    fun createDispatcher(): MainCoroutineDispatcher
}
