/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

public actual object Dispatchers {
    public actual val Default: CoroutineDispatcher = createDefaultDispatcher()
    public actual val Main: MainCoroutineDispatcher = createMainDispatcher(Default)
    public actual val Unconfined: CoroutineDispatcher get() = kotlinx.coroutines.Unconfined
}
internal expect fun createMainDispatcher(default: CoroutineDispatcher): MainCoroutineDispatcher

