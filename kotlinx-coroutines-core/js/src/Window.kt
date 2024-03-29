package kotlinx.coroutines

import org.w3c.dom.Window

/**
 * Converts an instance of [Window] to an implementation of [CoroutineDispatcher].
 */
public fun Window.asCoroutineDispatcher(): CoroutineDispatcher =
    @Suppress("UnsafeCastFromDynamic")
    asDynamic().coroutineDispatcher ?: WindowDispatcher(this).also {
        asDynamic().coroutineDispatcher = it
    }

/**
 * Suspends coroutine until next JS animation frame and returns frame time on resumption.
 * The time is consistent with [window.performance.now()][org.w3c.performance.Performance.now].
 * This function is cancellable. If the [Job] of the current coroutine is completed while this suspending
 * function is waiting, this function immediately resumes with [CancellationException].
 */
public suspend fun Window.awaitAnimationFrame(): Double = suspendCancellableCoroutine { cont ->
    asWindowAnimationQueue().enqueue(cont)
}

private fun Window.asWindowAnimationQueue(): WindowAnimationQueue =
    @Suppress("UnsafeCastFromDynamic")
    asDynamic().coroutineAnimationQueue ?: WindowAnimationQueue(this).also {
        asDynamic().coroutineAnimationQueue = it
    }

private class WindowAnimationQueue(private val window: Window) {
    private val dispatcher = window.asCoroutineDispatcher()
    private var scheduled = false
    private var current = ArrayDeque<CancellableContinuation<Double>>()
    private var next = ArrayDeque<CancellableContinuation<Double>>()
    private var timestamp = 0.0

    fun enqueue(cont: CancellableContinuation<Double>) {
        next.addLast(cont)
        if (!scheduled) {
            scheduled = true
            window.requestAnimationFrame { ts ->
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
        while(true) {
            val element = current.removeFirstOrNull() ?: return
            with(element) { dispatcher.resumeUndispatched(timestamp) }
        }
    }
}
