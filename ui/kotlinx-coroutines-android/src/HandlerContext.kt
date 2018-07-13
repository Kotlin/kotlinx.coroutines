/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.android

import android.os.*
import kotlinx.coroutines.*

/**
 * Dispatches execution onto Android main UI thread and provides native [delay][Delay.delay] support.
 * @suppress **Deprecated**: Use [Dispatchers.Main].
 */
@Deprecated(
    message = "Use Dispatchers.Main",
    replaceWith = ReplaceWith("Dispatchers.Main",
        imports = ["kotlinx.coroutines.Dispatchers", "kotlinx.coroutines.android.Main"])
)
val UI: HandlerContext
    get() = Dispatchers.Main as HandlerContext

@Deprecated(level = DeprecationLevel.HIDDEN, message = "Binary compatibility")
@JvmName("asCoroutineDispatcher")
public fun Handler.asCoroutineDispatcher0(): HandlerContext =
    HandlerContext(this)
