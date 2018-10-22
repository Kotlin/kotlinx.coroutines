/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

internal class InjectableDispatcherFactory : MainDispatcherFactory {

    override fun createDispatcher(): MainCoroutineDispatcher = InjectableMainDispatcher

    override val loadPriority: Int
        get() = Int.MAX_VALUE
}

internal object InjectableMainDispatcher : MainCoroutineDispatcher() {

    private var delegate: CoroutineDispatcher = Dispatchers.Unconfined

    public fun inject(dispatcher: CoroutineDispatcher) {
        delegate = dispatcher
    }

    override val immediate: MainCoroutineDispatcher = (delegate as? MainCoroutineDispatcher)?.immediate ?: this

    override fun isDispatchNeeded(context: CoroutineContext): Boolean = delegate.isDispatchNeeded(context)

    override fun dispatch(context: CoroutineContext, block: Runnable) = delegate.dispatch(context, block)
}
