/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*

/**
 * A coroutine dispatcher that is not confined to any specific thread.
 */
internal object Unconfined : CoroutineDispatcher() {
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = false
    // Just in case somebody wraps Unconfined dispatcher casing the "dispatch" to be called from "yield"
    override fun dispatch(context: CoroutineContext, block: Runnable) = block.run()
    override fun toString(): String = "Unconfined"
}
