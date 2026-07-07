package kotlinx.coroutines

import kotlin.js.*

/**
 * Converts an instance of [W3CWindow] to an implementation of [CoroutineDispatcher].
 */
@Suppress("EXPOSED_RECEIVER_TYPE")
@OptIn(ExperimentalWasmJsInterop::class)
public fun W3CWindow.asCoroutineDispatcher(): CoroutineDispatcher =
    @Suppress("UNCHECKED_CAST", "UNCHECKED_CAST_TO_EXTERNAL_INTERFACE")
    (windowGetCoroutineDispatcher(this) as? JsReference<WindowDispatcher>)?.get()
        ?: WindowDispatcher(this).also { windowSetCoroutineDispatcher(this, it.toJsReference()) }

/**
 * Suspends coroutine until next JS animation frame and returns frame time on resumption.
 * The time is consistent with [window.performance.now()][org.w3c.performance.Performance.now].
 * This function is cancellable. If the [Job] of the current coroutine is completed while this suspending
 * function is waiting, this function immediately resumes with [CancellationException].
 */
@Suppress("EXPOSED_RECEIVER_TYPE")
public suspend fun W3CWindow.awaitAnimationFrame(): Double = suspendCancellableCoroutine { cont ->
    asWindowAnimationQueue().enqueue(cont)
}

@OptIn(ExperimentalWasmJsInterop::class)
private fun W3CWindow.asWindowAnimationQueue(): WindowAnimationQueue =
    @Suppress("UNCHECKED_CAST", "UNCHECKED_CAST_TO_EXTERNAL_INTERFACE")
    (windowGetCoroutineAnimationQueue(this) as? JsReference<WindowAnimationQueue>)?.get()
        ?: WindowAnimationQueue(this).also { windowSetCoroutineAnimationQueue(this, it.toJsReference()) }

private class WindowAnimationQueue(private val window: W3CWindow) {
    private val dispatcher = window.asCoroutineDispatcher()
    private var scheduled = false
    private var current = ArrayDeque<CancellableContinuation<Double>>()
    private var next = ArrayDeque<CancellableContinuation<Double>>()
    private var timestamp = 0.0

    fun enqueue(cont: CancellableContinuation<Double>) {
        next.addLast(cont)
        if (!scheduled) {
            scheduled = true
            w3cRequestAnimationFrame(window) { ts ->
                timestamp = ts
                val prev = current
                current = next
                next = prev
                scheduled = false
                process()
            }
        }
    }

    fun process() {
        while (true) {
            val element = current.removeFirstOrNull() ?: return
            with(element) { dispatcher.resumeUndispatched(timestamp) }
        }
    }
}

// [WindowDispatcher] and [WindowAnimationQueue] instances used to be cached on the window object itself via
// `asDynamic().coroutineDispatcher = ...`, but `dynamic` is a js-only feature and unavailable on wasmJs.
// This caching is not just an optimization: repeated calls to [asCoroutineDispatcher] / [awaitAnimationFrame]
// on the same window must reuse the same instance, or [WindowMessageQueue]'s init block re-registers a
// `message` event listener on every call. We attach a [JsReference] to the window instead, the same technique
// `promiseSetDeferred` / `promiseGetDeferred` use in Promise.kt to cache a [Deferred] on a [Promise].

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
private fun windowSetCoroutineDispatcher(window: W3CWindow, dispatcher: JsAny): Unit =
    js("window.coroutineDispatcher = dispatcher")

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
private fun windowGetCoroutineDispatcher(window: W3CWindow): JsAny? =
    js("window.coroutineDispatcher == null ? null : window.coroutineDispatcher")

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
private fun windowSetCoroutineAnimationQueue(window: W3CWindow, queue: JsAny): Unit =
    js("window.coroutineAnimationQueue = queue")

@OptIn(ExperimentalWasmJsInterop::class)
@Suppress("UNUSED_PARAMETER")
private fun windowGetCoroutineAnimationQueue(window: W3CWindow): JsAny? =
    js("window.coroutineAnimationQueue == null ? null : window.coroutineAnimationQueue")
