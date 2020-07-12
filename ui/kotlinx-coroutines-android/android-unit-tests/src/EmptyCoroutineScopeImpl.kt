/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.android

import kotlinx.coroutines.*
import kotlin.coroutines.*

// Classes for testing service loader
internal class EmptyCoroutineScopeImpl1 : CoroutineScope {
    override val coroutineContext: CoroutineContext
        get() = EmptyCoroutineContext
}

internal class EmptyCoroutineScopeImpl2 : CoroutineScope {
    override val coroutineContext: CoroutineContext
        get() = EmptyCoroutineContext
}

internal class EmptyCoroutineScopeImpl3 : CoroutineScope {
    override val coroutineContext: CoroutineContext
        get() = EmptyCoroutineContext
}
