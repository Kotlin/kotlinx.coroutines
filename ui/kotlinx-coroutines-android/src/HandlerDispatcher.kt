/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

@file:Suppress("unused")

package kotlinx.coroutines.experimental.android

import android.os.*
import android.support.annotation.*
import android.view.*
import kotlinx.coroutines.experimental.*
import kotlinx.coroutines.experimental.internal.MainDispatcherFactory
import java.lang.reflect.Constructor
import kotlin.coroutines.experimental.*

/**
 * Dispatches execution onto Android main thread and provides native [delay][Delay.delay] support.
 */
@Deprecated(level = DeprecationLevel.HIDDEN, message = "Deprecated in favor of Dispatchers property")
public val Dispatchers.Main: HandlerDispatcher
    get() = MainDispatcher

/**
 * Dispatches execution onto Android [Handler].
 *
 * This class provides type-safety and a point for future extensions.
 */
public sealed class HandlerDispatcher : MainCoroutineDispatcher(), Delay {
    /**
     * Returns dispatcher that executes coroutines immediately when it is already in the right handler context
     * (current looper is the same as this handler's looper). See [isDispatchNeeded] documentation on
     * why this should not be done by default.
     *
     * **Note: This is an experimental api.** Semantics of this dispatcher may change in the future.
     */
    @ExperimentalCoroutinesApi
    public abstract override val immediate: HandlerDispatcher
}

@Keep
internal class AndroidDispatcherFactory : MainDispatcherFactory {
    override fun createDispatcher(): MainCoroutineDispatcher = Main

    override val loadPriority: Int
        get() = Int.MAX_VALUE
}

/**
 * Represents an arbitrary [Handler] as a implementation of [CoroutineDispatcher]
 * with an optional [name] for nicer debugging
 */
@JvmName("from") // this is for a nice Java API, see issue #255
@JvmOverloads
public fun Handler.asCoroutineDispatcher(name: String? = null): HandlerDispatcher =
    HandlerContext(this, name)

private const val MAX_DELAY = Long.MAX_VALUE / 2 // cannot delay for too long on Android

internal val mainHandler = Looper.getMainLooper().asHandler(async = true)

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

@JvmField // this is for a nice Java API, see issue #255
internal val Main: HandlerDispatcher = HandlerContext(mainHandler, "Main")

private val MainDispatcher: HandlerDispatcher = Main // Alias

/**
 * Implements [CoroutineDispatcher] on top of an arbitrary Android [Handler].
 * @suppress **Deprecated**: Use [HandlerDispatcher].
 */
@Deprecated(
    message = "Use HandlerDispatcher",
    replaceWith = ReplaceWith("HandlerDispatcher",
        imports = ["kotlinx.coroutines.experimental.android.HandlerDispatcher"])
)
public class HandlerContext private constructor(
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
    public constructor(
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
        handler.post(block)
    }

    override fun scheduleResumeAfterDelay(timeMillis: Long, continuation: CancellableContinuation<Unit>) {
        val block = Runnable {
            with(continuation) { resumeUndispatched(Unit) }
        }
        handler.postDelayed(block, timeMillis.coerceAtMost(MAX_DELAY))
        continuation.invokeOnCancellation { handler.removeCallbacks(block) }
    }

    override fun invokeOnTimeout(timeMillis: Long, block: Runnable): DisposableHandle {
        handler.postDelayed(block, timeMillis.coerceAtMost(MAX_DELAY))
        return object : DisposableHandle {
            override fun dispose() {
                handler.removeCallbacks(block)
            }
        }
    }

    /**
     * Awaits the next animation frame and returns frame time in nanoseconds.
     * @suppress **Deprecated**: Use top-level [awaitFrame].
     */
    @Deprecated(
        message = "Use top-level awaitFrame",
        replaceWith = ReplaceWith("kotlinx.coroutines.experimental.android.awaitFrame()")
    )
    public suspend fun awaitFrame(): Long =
        kotlinx.coroutines.experimental.android.awaitFrame()

    override fun toString(): String =
        if (name != null) {
            if (invokeImmediately) "$name [immediate]" else name
        } else {
            handler.toString()
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
        mainHandler.post {
            updateChoreographerAndPostFrameCallback(cont)
        }
    }
}

private fun updateChoreographerAndPostFrameCallback(cont: CancellableContinuation<Long>) {
    val choreographer = choreographer ?:
    Choreographer.getInstance()!!.also { choreographer = it }
    postFrameCallback(choreographer, cont)
}

private fun postFrameCallback(choreographer: Choreographer, cont: CancellableContinuation<Long>) {
    choreographer.postFrameCallback { nanos ->
        with(cont) { Main.resumeUndispatched(nanos) }
    }
}
