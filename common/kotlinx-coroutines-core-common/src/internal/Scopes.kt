/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.experimental.internal

import kotlinx.coroutines.experimental.*
import kotlin.coroutines.experimental.*

/**
 * This is a coroutine instance that is created by [coroutineScope] builder.
 * It is just a vanilla instance of [AbstractCoroutine].
 */
internal class ScopeCoroutine<R>(
    parentContext: CoroutineContext
) : AbstractCoroutine<R>(parentContext, true)

internal class ContextScope(context: CoroutineContext) : CoroutineScope {
    override val coroutineContext: CoroutineContext = context
}
