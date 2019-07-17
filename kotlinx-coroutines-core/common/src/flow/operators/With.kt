/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:JvmMultifileClass
@file:JvmName("FlowKt")
@file:Suppress("UNCHECKED_CAST")

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.internal.*
import kotlin.jvm.*

// todo: KDoc
public fun <T, R> Flow<T>.with(block: suspend CoroutineScopeWithFlow<T>.() -> Flow<R>): Flow<R> = scopedFlow { collector ->
    val scope = CoroutineScopeWithFlow(this, this@with)
    try {
        block(scope).collect(collector)
    } finally {
        coroutineContext[Job]!!.cancelChildren(AbortFlowException())
    }
}

// todo: KDoc
public class CoroutineScopeWithFlow<T> internal constructor(
    scope: CoroutineScope,
    flow: Flow<T>
): CoroutineScope by scope, Flow<T> by flow

// todo: KDoc
@Suppress("SuspendFunctionOnCoroutineScope")
public suspend fun <T> CoroutineScopeWithFlow<*>.stateOf(flow: Flow<T>): StateFlow<T> {
    val state = flow as? StateFlow<T> ?: createState(flow)
    return state.awaitInitialized()
}

private fun <T> CoroutineScope.createState(flow: Flow<T>): MutableStateFlow<T> {
    val state = StateFlow<T>()
    launch(start = CoroutineStart.UNDISPATCHED) {
        flow.collect { state.value = it }
    }
    return state
}

// todo: KDoc
public fun <A, B, R> Flow<A>.withStateOf(other: Flow<B>, transform: suspend (A, B) -> R) =
    with {
        val b by stateOf(other)
        map { a -> transform(a, b) }
    }
