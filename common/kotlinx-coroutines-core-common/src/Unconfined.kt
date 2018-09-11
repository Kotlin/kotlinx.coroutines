/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.*

/**
 * A coroutine dispatcher that is not confined to any specific thread.
 * @suppress **Deprecated**: Use [Dispatchers.Unconfined].
 */
@Deprecated(
    message = "Use Dispatchers.Unconfined",
    replaceWith = ReplaceWith("Dispatchers.Unconfined",
        imports = ["kotlinx.coroutines.experimental.Dispatchers"])
)
// todo: This will become an internal implementation object
public object Unconfined : CoroutineDispatcher() {
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = false
    override fun dispatch(context: CoroutineContext, block: Runnable) { throw UnsupportedOperationException() }
    override fun toString(): String = "Unconfined"
}
