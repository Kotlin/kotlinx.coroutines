/*
 * Copyright 2016-2017 JetBrains s.r.o.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package kotlinx.coroutines.experimental

import kotlin.coroutines.experimental.AbstractCoroutineContextElement
import kotlin.coroutines.experimental.CoroutineContext


/**
 * Helper function for coroutine builder implementations to handle uncaught exception in coroutines.
 * It tries to handle uncaught exception in the following way:
 * * If there is [CoroutineExceptionHandler] in the context, then it is used.
 * * Otherwise, if exception is [CancellationException] then it is ignored
 *   (because that is the supposed mechanism to cancel the running coroutine)
 * * Otherwise, if there is a [Job] in the context, then [Job.cancel] is invoked and if it
 *   returns `true` (it was still active), then the exception is considered to be handled.
 * * Otherwise, current thread's [Thread.uncaughtExceptionHandler] is used.
 */
fun handleCoroutineException(context: CoroutineContext, exception: Throwable) {
    context[CoroutineExceptionHandler]?.let {
        it.handleException(context, exception)
        return
    }
    // ignore CancellationException (they are normal means to terminate a coroutine)
    if (exception is CancellationException) return
    // quit if successfully pushed exception as cancellation reason
    if (context[Job]?.cancel(exception) ?: false) return
    // otherwise just use thread's handler
    val currentThread = Thread.currentThread()
    currentThread.uncaughtExceptionHandler.uncaughtException(currentThread, exception)
}

/**
 * An optional element on the coroutine context to handle uncaught exceptions.
 * See [handleCoroutineException].
 */
public interface CoroutineExceptionHandler : CoroutineContext.Element {
    /**
     * Key for [CoroutineExceptionHandler] instance in the coroutine context.
     */
    companion object Key : CoroutineContext.Key<CoroutineExceptionHandler> {
        /**
         * Creates new [CoroutineExceptionHandler] instance.
         * @param handler a function which handles exception thrown by a coroutine
         * @suppress **Deprecated**
         */
        @Deprecated("Replaced with top-level function", level = DeprecationLevel.HIDDEN)
        public operator inline fun invoke(crossinline handler: (CoroutineContext, Throwable) -> Unit): CoroutineExceptionHandler =
           CoroutineExceptionHandler(handler)
    }

    /**
     * Handles uncaught [exception] in the given [context]. It is invoked
     * if coroutine has an uncaught exception. See [handleCoroutineException].
     */
    public fun handleException(context: CoroutineContext, exception: Throwable)
}

/**
 * Creates new [CoroutineExceptionHandler] instance.
 * @param handler a function which handles exception thrown by a coroutine
 */
public inline fun CoroutineExceptionHandler(crossinline handler: (CoroutineContext, Throwable) -> Unit): CoroutineExceptionHandler =
    object: AbstractCoroutineContextElement(CoroutineExceptionHandler), CoroutineExceptionHandler {
        override fun handleException(context: CoroutineContext, exception: Throwable) =
            handler.invoke(context, exception)
    }