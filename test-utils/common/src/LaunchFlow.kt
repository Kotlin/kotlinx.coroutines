/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.flow

import kotlinx.coroutines.*
import kotlin.jvm.*
import kotlin.reflect.*

public typealias Handler<T> = suspend CoroutineScope.(T) -> Unit

/*
 * Design of this builder is not yet stable, so leaving it as is.
 */
public class LaunchFlowBuilder<T> {
    /*
     * NB: this implementation is a temporary ad-hoc (and slightly incorrect)
     * solution until coroutine-builders are ready
     *
     * NB 2: this internal stuff is required to workaround KT-30795
     */
    @PublishedApi
    internal var onEach: Handler<T>? = null
    @PublishedApi
    internal var finally: Handler<Throwable?>? = null
    @PublishedApi
    internal var exceptionHandlers = LinkedHashMap<KClass<*>, Handler<Throwable>>()

    public fun onEach(action: suspend CoroutineScope.(value: T) -> Unit) {
        check(onEach == null) { "onEach block is already registered" }
        check(exceptionHandlers.isEmpty()) { "onEach block should be registered before exceptionHandlers block" }
        check(finally == null) { "onEach block should be registered before finally block" }
        onEach = action
    }

    public inline fun <reified T : Throwable> catch(noinline action: suspend CoroutineScope.(T) -> Unit) {
        check(onEach != null) { "onEach block should be registered first" }
        check(finally == null) { "exceptionHandlers block should be registered before finally block" }
        @Suppress("UNCHECKED_CAST")
            exceptionHandlers[T::class] = action as Handler<Throwable>
    }

    public fun finally(action: suspend CoroutineScope.(cause: Throwable?) -> Unit) {
        check(finally == null) { "Finally block is already registered" }
        check(onEach != null) { "onEach block should be registered before finally block" }
        if (finally == null) finally = action
    }

    internal fun build(): Handlers<T> =
        Handlers(onEach ?: error("onEach is not registered"), exceptionHandlers, finally)
}

internal class Handlers<T>(
    @JvmField
    internal var onEach: Handler<T>,
    @JvmField
    internal var exceptionHandlers: Map<KClass<*>, Handler<Throwable>>,
    @JvmField
    internal var finally: Handler<Throwable?>?
)

private fun <T> CoroutineScope.launchFlow(
    flow: Flow<T>,
    builder: LaunchFlowBuilder<T>.() -> Unit
): Job {
    val handlers = LaunchFlowBuilder<T>().apply(builder).build()
    return launch {
        var caught: Throwable? = null
        try {
            coroutineScope {
                flow.collect { value ->
                    handlers.onEach(this, value)
                }
            }
        } catch (e: Throwable) {
            handlers.exceptionHandlers.forEach { (key, value) ->
                if (key.isInstance(e)) {
                    caught = e
                    value.invoke(this, e)
                    return@forEach
                }
            }
            if (caught == null) {
                caught = e
                throw e
            }
        } finally {
            cancel() // TODO discuss
            handlers.finally?.invoke(CoroutineScope(coroutineContext + NonCancellable), caught)
        }
    }
}

public fun <T> Flow<T>.launchIn(
    scope: CoroutineScope,
    builder: LaunchFlowBuilder<T>.() -> Unit
): Job = scope.launchFlow(this, builder)
