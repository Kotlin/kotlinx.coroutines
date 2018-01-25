package kotlinx.coroutines.debug.manager

import kotlin.coroutines.experimental.Continuation

class WrappedCompletion(val completion: Continuation<Any?>) : Continuation<Any?> {
    override val context = completion.context

    override fun resume(value: Any?) {
        StacksManager.handleCoroutineExit(this)
        completion.resume(value)
    }

    override fun resumeWithException(exception: Throwable) {
        StacksManager.handleCoroutineExit(this)
        completion.resumeWithException(exception)
    }

    override fun toString(): String = completion.toString()
}
