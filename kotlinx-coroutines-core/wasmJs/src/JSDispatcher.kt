package kotlinx.coroutines

import org.w3c.dom.Window
import kotlin.js.*

public actual typealias W3CWindow = Window

internal actual fun w3cSetTimeout(window: W3CWindow, handler: () -> Unit, timeout: Int): Int =
    setTimeout(window, handler, timeout)

internal actual fun w3cSetTimeout(handler: () -> Unit, timeout: Int): Int =
    setTimeout(handler, timeout)

internal actual fun w3cClearTimeout(window: W3CWindow, handle: Int) =
    window.clearTimeout(handle)

internal actual fun w3cClearTimeout(handle: Int) =
    clearTimeout(handle)

internal actual class ScheduledMessageQueue actual constructor(private val dispatcher: SetTimeoutBasedDispatcher) : MessageQueue() {
    internal val processQueue: () -> Unit = ::process

    actual override fun schedule() {
        dispatcher.scheduleQueueProcessing()
    }

    actual override fun reschedule() {
        setTimeout(processQueue, 0)
    }

    internal actual fun setTimeout(timeout: Int) {
        setTimeout(processQueue, timeout)
    }
}

internal class NodeDispatcher(private val process: JsProcess) : SetTimeoutBasedDispatcher() {
    override fun scheduleQueueProcessing() {
        process.nextTick(messageQueue.processQueue)
    }
}

@Suppress("UNUSED_PARAMETER")
private fun subscribeToWindowMessages(window: Window, process: () -> Unit): Unit = js("""{
    const handler = (event) => {
        if (event.source == window && event.data == 'dispatchCoroutine') {
            event.stopPropagation();
            process();
        }
    }
    window.addEventListener('message', handler, true);
}""")

@Suppress("UNUSED_PARAMETER")
private fun createRescheduleMessagePoster(window: Window): () -> Unit =
    js("() => window.postMessage('dispatchCoroutine', '*')")

@Suppress("UNUSED_PARAMETER")
private fun createScheduleMessagePoster(process: () -> Unit): () -> Unit =
    js("() => Promise.resolve(0).then(process)")

internal actual class WindowMessageQueue actual constructor(window: W3CWindow) : MessageQueue() {
    private val scheduleMessagePoster = createScheduleMessagePoster(::process)
    private val rescheduleMessagePoster = createRescheduleMessagePoster(window)
    init {
        subscribeToWindowMessages(window, ::process)
    }

    actual override fun schedule() {
        scheduleMessagePoster()
    }

    actual override fun reschedule() {
        rescheduleMessagePoster()
    }
}

// We need to reference global setTimeout and clearTimeout so that it works on Node.JS as opposed to
// using them via "window" (which only works in browser)
private external fun setTimeout(handler: () -> Unit, timeout: Int): Int

// d8 doesn't have clearTimeout
@Suppress("UNUSED_PARAMETER")
private fun clearTimeout(handle: Int): Unit =
    js("{ if (typeof clearTimeout !== 'undefined') clearTimeout(handle); }")

@Suppress("UNUSED_PARAMETER")
private fun setTimeout(window: Window, handler: () -> Unit, timeout: Int): Int =
    js("window.setTimeout(handler, timeout)")
