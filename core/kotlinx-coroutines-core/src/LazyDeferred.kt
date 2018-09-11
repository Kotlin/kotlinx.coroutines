/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*

/**
 * @suppress **Deprecated**: `Deferred` incorporates functionality of `LazyDeferred`. See [Deferred].
 */
@Deprecated(message = "`Deferred` incorporates functionality of `LazyDeferred`", level = DeprecationLevel.WARNING,
        replaceWith = ReplaceWith("Deferred"))
typealias LazyDeferred<T> = Deferred<T>

/**
 * @suppress **Deprecated**: Replace with `async(context, start = false) { ... }`. See [CoroutineScope.async].
 */
@Suppress("DEPRECATION")
@Deprecated(message = "This functionality is incorporated into `async", level = DeprecationLevel.WARNING,
        replaceWith = ReplaceWith("async(context, start = false, block = block)"))
public fun <T> lazyDefer(context: CoroutineContext, block: suspend CoroutineScope.() -> T) : Deferred<T> =
    async(context, start = false, block = block)
