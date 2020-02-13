/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow.internal

import kotlinx.coroutines.*
import kotlinx.coroutines.flow.*
import kotlinx.coroutines.internal.ScopeCoroutine
import kotlin.coroutines.*
import kotlin.jvm.*

internal expect class SafeCollector<T>(
    collector: FlowCollector<T>,
    collectContext: CoroutineContext
) : FlowCollector<T> {
    internal val collector: FlowCollector<T>
    internal val collectContext: CoroutineContext
    internal val collectContextSize: Int
    public fun releaseIntercepted()
}

@JvmName("checkContext") // For prettier stack traces
internal fun SafeCollector<*>.checkContext(currentContext: CoroutineContext) {
    val result = currentContext.fold(0) fold@{ count, element ->
        val key = element.key
        val collectElement = collectContext[key]
        if (key !== Job) {
            return@fold if (element !== collectElement) Int.MIN_VALUE
            else count + 1
        }

        val collectJob = collectElement as Job?
        val emissionParentJob = (element as Job).transitiveCoroutineParent(collectJob)
        /*
         * Code like
         * ```
         * coroutineScope {
         *     launch {
         *         emit(1)
         *     }
         *
         *     launch {
         *         emit(2)
         *     }
         * }
         * ```
         * is prohibited because 'emit' is not thread-safe by default. Use 'channelFlow' instead if you need concurrent emission
         * or want to switch context dynamically (e.g. with `withContext`).
         *
         * Note that collecting from another coroutine is allowed, e.g.:
         * ```
         * coroutineScope {
         *     val channel = produce {
         *         collect { value ->
         *             send(value)
         *         }
         *     }
         *     channel.consumeEach { value ->
         *         emit(value)
         *     }
         * }
         * ```
         * is a completely valid.
         */
        if (emissionParentJob !== collectJob) {
            error(
                "Flow invariant is violated:\n" +
                        "\t\tEmission from another coroutine is detected.\n" +
                        "\t\tChild of $emissionParentJob, expected child of $collectJob.\n" +
                        "\t\tFlowCollector is not thread-safe and concurrent emissions are prohibited.\n" +
                        "\t\tTo mitigate this restriction please use 'channelFlow' builder instead of 'flow'"
            )
        }

        /*
         * If collect job is null (-> EmptyCoroutineContext, probably run from `suspend fun main`), then invariant is maintained
         * (common transitive parent is "null"), but count check will fail, so just do not count job context element when
         * flow is collected from EmptyCoroutineContext
         */
        if (collectJob == null) count else count + 1
    }
    if (result != collectContextSize) {
        error(
            "Flow invariant is violated:\n" +
                    "\t\tFlow was collected in $collectContext,\n" +
                    "\t\tbut emission happened in $currentContext.\n" +
                    "\t\tPlease refer to 'flow' documentation or use 'flowOn' instead"
        )
    }
}

internal tailrec fun Job?.transitiveCoroutineParent(collectJob: Job?): Job? {
    if (this === null) return null
    if (this === collectJob) return this
    if (this !is ScopeCoroutine<*>) return this
    return parent.transitiveCoroutineParent(collectJob)
}

/**
 * An analogue of the [flow] builder that does not check the context of execution of the resulting flow.
 * Used in our own operators where we trust the context of invocations.
 */
@PublishedApi
internal inline fun <T> unsafeFlow(@BuilderInference crossinline block: suspend FlowCollector<T>.() -> Unit): Flow<T> {
    return object : Flow<T> {
        override suspend fun collect(collector: FlowCollector<T>) {
            collector.block()
        }
    }
}
