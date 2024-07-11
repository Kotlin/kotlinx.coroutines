package kotlinx.coroutines

import org.w3c.dom.*
import kotlin.js.Promise

internal actual typealias W3CWindow = Window

internal actual fun w3cSetTimeout(window: W3CWindow, handler: () -> Unit, timeout: Int): Int =
    setTimeout(window, handler, timeout)

internal actual fun w3cSetTimeout(handler: () -> Unit, timeout: Int): Int =
    setTimeout(handler, timeout)

internal actual fun w3cClearTimeout(window: W3CWindow, handle: Int) =
    window.clearTimeout(handle)

internal actual fun w3cClearTimeout(handle: Int) =
    clearTimeout(handle)

internal actual class ScheduledMessageQueue actual constructor(private val dispatcher: SetTimeoutBasedDispatcher) : MessageQueue() {
    internal val processQueue: dynamic = { process() }

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

internal object NodeDispatcher : SetTimeoutBasedDispatcher() {
    override fun scheduleQueueProcessing() {
        process.nextTick(messageQueue.processQueue)
    }
}

internal actual class WindowMessageQueue actual constructor(private val window: W3CWindow) : MessageQueue() {
    private val messageName = "dispatchCoroutine"

    init {
        window.addEventListener("message", { event: dynamic ->
            if (event.source == window && event.data == messageName) {
                event.stopPropagation()
                process()
            }
        }, true)
    }

    actual override fun schedule() {
        Promise.resolve(Unit).then({ process() })
    }

    actual override fun reschedule() {
        window.postMessage(messageName, "*")
    }
}

// We need to reference global setTimeout and clearTimeout so that it works on Node.JS as opposed to
// using them via "window" (which only works in browser)
private external fun setTimeout(handler: dynamic, timeout: Int = definedExternally): Int

private external fun clearTimeout(handle: Int = definedExternally)

private fun setTimeout(window: Window, handler: () -> Unit, timeout: Int): Int =
    window.setTimeout(handler, timeout)
