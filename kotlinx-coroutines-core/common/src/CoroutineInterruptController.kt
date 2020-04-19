/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlin.coroutines.AbstractCoroutineContextElement
import kotlin.coroutines.CoroutineContext

/**
 * This [CoroutineContext] element makes a coroutine interruptible.
 *
 * With this element, the thread executing the coroutine is interrupted when the coroutine is canceled, making
 * blocking procedures stop. Exceptions that indicate an interrupted procedure, eg., InterruptedException on JVM
 * are transformed into [CancellationException] at the end of the coroutine. Thus, everything else goes as if this
 * element is not present. In particular, the parent coroutine won't be canceled by those exceptions.
 *
 * This is an abstract element and will be implemented by each individual platform (or won't be implemented).
 * The JVM implementation is named CoroutineInterruptible.
 *
 * Example:
 * ```
 * GlobalScope.launch(Dispatchers.IO + CoroutineInterruptible) {
 *     async {
 *         // This block will throw [CancellationException] instead of an exception indicating
 *         // interruption, such as InterruptedException on JVM.
 *         withContext(CoroutineName) {
 *             doSomethingUseful()
 *
 *             // This blocking procedure will be interrupted when this coroutine is canceled
 *             // by Exception thrown by the below async block.
 *             doSomethingElseUsefulInterruptible()
 *         }
 *     }
 *
 *     async {
 *        delay(500L)
 *        throw Exception()
 *     }
 * }
 * ```
 */
abstract class CoroutineInterruptController : AbstractCoroutineContextElement(Key) {
    /**
     * Key for [CoroutineInterruptController] instance in the coroutine context.
     */
    @InternalCoroutinesApi
    companion object Key : CoroutineContext.Key<CoroutineInterruptController>

    /**
     * Update the complete state of a coroutine, mainly for exception transformation.
     */
    @InternalCoroutinesApi
    abstract fun updateCoroutineCompleteState(completeState: Any?): Any?
}