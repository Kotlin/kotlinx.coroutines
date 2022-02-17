/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")

package kotlinx.coroutines.android

import android.os.*
import android.view.*
import androidx.annotation.*
import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import java.lang.reflect.*
import kotlin.coroutines.*

/**
 * Dispatches execution onto Android [Handler].
 *
 * This class provides type-safety and a point for future extensions.
 */
public sealed class HandlerDispatcher : MainCoroutineDispatcher(), Delay {
    /**
     * Returns dispatcher that executes coroutines immediately when it is already in the right context
     * (current looper is the same as this handler's looper) without an additional [re-dispatch][CoroutineDispatcher.dispatch].
     * This dispatcher does not use [Handler.post] when current looper is the same as looper of the handler.
     *
     * Immediate dispatcher is safe from stack overflows and in case of nested invocations forms event-loop similar to [Dispatchers.Unconfined].
     * The event loop is an advanced topic and its implications can be found in [Dispatchers.Unconfined] documentation.
     *
     * Example of usage:
     * ```
     * suspend fun updateUiElement(val text: String) {
     *   /*
     *    * If it is known that updateUiElement can be invoked both from the Main thread and from other threads,
     *    * `immediate` dispatcher is used as a performance optimization to avoid unnecessary dispatch.
     *    *
     *    * In that case, when `updateUiElement` is invoked from the Main thread, `uiElement.text` will be
     *    * invoked immediately without any dispatching, otherwise, the `Dispatchers.Main` dispatch cycle via
     *    * `Handler.post` will be triggered.
     *    */
     *   withContext(Dispatchers.Main.immediate) {
     *     uiElement.text = text
     *   }
     *   // Do context-independent logic such as logging
     * }
     * ```
     */
    public abstract override val immediate: HandlerDispatcher
}

internal class AndroidDispatcherFactory : MainDispatcherFactory {

    override fun createDispatcher(allFactories: List<MainDispatcherFactory>) =
        HandlerContext(Looper.getMainLooper().asHandler(async = true))

    override fun hintOnError(): String = "For tests Dispatchers.setMain from kotlinx-coroutines-test module can be used"

    override val loadPriority: Int
        get() = Int.MAX_VALUE / 2
}

/**
 * Represents an arbitrary [Handler] as an implementation of [CoroutineDispatcher]
 * with an optional [name] for nicer debugging
 *
 * ## Rejected execution
 *
 * If the underlying handler is closed and its message-scheduling methods start to return `false` on
 * an attempt to submit a continuation task to the resulting dispatcher,
 * then the [Job] of the affected task is [cancelled][Job.cancel] and the task is submitted to the
 * [Dispatchers.IO], so that the affected coroutine can cleanup its resources and promptly complete.
 */
@JvmName("from") // this is for a nice Java API, see issue #255
@JvmOverloads
public fun Handler.asCoroutineDispatcher(name: String? = null): HandlerDispatcher =
    HandlerContext(this, name)

private const val MAX_DELAY = Long.MAX_VALUE / 2 // cannot delay for too long on Android

@VisibleForTesting
internal fun Looper.asHandler(async: Boolean): Handler {
    // Async support was added in API 16.
    if (!async || Build.VERSION.SDK_INT < 16) {
        return Handler(this)
    }

    if (Build.VERSION.SDK_INT >= 28) {
        // TODO compile against API 28 so this can be invoked without reflection.
        val factoryMethod = Handler::class.java.getDeclaredMethod("createAsync", Looper::class.java)
        return factoryMethod.invoke(null, this) as Handler
    }

    val constructor: Constructor<Handler>
    try {
        constructor = Handler::class.java.getDeclaredConstructor(Looper::class.java,
            Handler.Callback::class.java, Boolean::class.javaPrimitiveType)
    } catch (ignored: NoSuchMethodException) {
        // Hidden constructor absent. Fall back to non-async constructor.
        return Handler(this)
    }
    return constructor.newInstance(this, null, true)
}

@JvmField
@Deprecated("Use Dispatchers.Main instead", level = DeprecationLevel.HIDDEN)
internal val Main: HandlerDispatcher? = runCatching { HandlerContext(Looper.getMainLooper().asHandler(async = true)) }.getOrNull()

/**
 * Implements [CoroutineDispatcher] on top of an arbitrary Android [Handler].
 */
internal class HandlerContext private constructor(
    private val handler: Handler,
    private val name: String?,
    private val invokeImmediately: Boolean
) : HandlerDispatcher(), Delay {
    /**
     * Creates [CoroutineDispatcher] for the given Android [handler].
     *
     * @param handler a handler.
     * @param name an optional name for debugging.
     */
    constructor(
        handler: Handler,
        name: String? = null
    ) : this(handler, name, false)

    @Volatile
    private var _immediate: HandlerContext? = if (invokeImmediately) this else null

    override val immediate: HandlerContext = _immediate ?:
        HandlerContext(handler, name, true).also { _immediate = it }

    override fun isDispatchNeeded(context: CoroutineContext): Boolean {
        return !invokeImmediately || Looper.myLooper() != handler.looper
    }

    override fun dispatch(context: CoroutineContext, block: Runnable) {
        if (!handler.post(block)) {
            cancelOnRejection(context, block)
        }
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val block = Runnable {
            with(continuation) { resumeUndispatched(Unit) }
        }
        if (handler.postDelayed(block, timeMillis.coerceAtMost(MAX_DELAY))) {
            continuation.invokeOnCancellation { handler.removeCallbacks(block) }
        } else {
            cancelOnRejection(continuation.context, block)
        }
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable, context: CoroutineContext): DisposableHandle {
        if (handler.postDelayed(block, timeMillis.coerceAtMost(MAX_DELAY))) {
            return DisposableHandle { handler.removeCallbacks(block) }
        }
        cancelOnRejection(context, block)
        return NonDisposableHandle
    }

    private fun cancelOnRejection(context: CoroutineContext, block: Runnable) {
        context.cancel(CancellationException("The task was rejected, the handler underlying the dispatcher '${toString()}' was closed"))
        Dispatchers.IO.dispatch(context, block)
    }

    override fun toString(): String = toStringInternalImpl() ?: run {
        val str = name ?: handler.toString()
        if (invokeImmediately) "$str.immediate" else str
    }

    override fun equals(other: Any?): Boolean = other is HandlerContext && other.handler === handler
    override fun hashCode(): Int = System.identityHashCode(handler)
}

@Volatile
private var choreographer: Choreographer? = null

/**
 * Awaits the next animation frame and returns frame time in nanoseconds.
 */
public suspend fun awaitFrame(): Long {
    // fast path when choreographer is already known
    val choreographer = choreographer
    if (choreographer != null) {
        return suspendCancellableCoroutine { cont ->
            postFrameCallback(choreographer, cont)
        }
    }
    // post into looper thread thread to figure it out
    return suspendCancellableCoroutine { cont ->
        Dispatchers.Main.dispatch(EmptyCoroutineContext, Runnable {
            updateChoreographerAndPostFrameCallback(cont)
        })
    }
}

private fun updateChoreographerAndPostFrameCallback(cont: CancellableContinuation<Long>) {
    val choreographer = choreographer ?:
    Choreographer.getInstance()!!.also { choreographer = it }
    postFrameCallback(choreographer, cont)
}

private fun postFrameCallback(choreographer: Choreographer, cont: CancellableContinuation<Long>) {
    choreographer.postFrameCallback { nanos ->
        with(cont) { Dispatchers.Main.resumeUndispatched(nanos) }
    }
}
