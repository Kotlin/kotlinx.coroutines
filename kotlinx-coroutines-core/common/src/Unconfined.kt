/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.*
import kotlin.jvm.*

/**
 * A coroutine dispatcher that is not confined to any specific thread.
 */
internal object Unconfined : CoroutineDispatcher() {
    override fun isDispatchNeeded(context: CoroutineContext): Boolean = false

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        // Just in case somebody wraps Unconfined dispatcher casing the "dispatch" to be called from "yield"
        // See also code of "yield" function
        val yieldContext = context[YieldContext]
        if (yieldContext != null) {
            // report to "yield" that it is an unconfined dispatcher and don't call "block.run()"
            yieldContext.dispatcherWasUnconfined = true
            return
        }
        block.run()
    }
    
    override fun toString(): String = "Unconfined"
}

/**
 * Used to detect calls to [Unconfined.dispatch] from [yield] function.
 */
internal class YieldContext : AbstractCoroutineContextElement(Key) {
    companion object Key : CoroutineContext.Key<YieldContext>

    @JvmField
    var dispatcherWasUnconfined = false
}