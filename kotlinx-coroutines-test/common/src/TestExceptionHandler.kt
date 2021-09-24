/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.test

import kotlinx.coroutines.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*

/**
 * A [CoroutineExceptionHandler] connected to a [TestCoroutineScope].
 *
 * This function accepts a [handler] that describes how to handle uncaught exceptions during tests; see
 * [CoroutineExceptionHandler] for details. As opposed to [CoroutineExceptionHandler], however, this has access to the
 * [TestCoroutineScope], which allows [cancelling][CoroutineScope.cancel] it or
 * [reporting][TestCoroutineScope.reportException] the error so that it is thrown on the call to
 * [TestCoroutineScope.cleanupTestCoroutines].
 *
 * If [linkedScope] is `null`, the [CoroutineExceptionHandler] returned from this function has special behavior when
 * passed to [createTestCoroutineScope]: the newly-created scope is linked to this handler. If [linkedScope] is not
 * null, then the resulting [CoroutineExceptionHandler] will be linked to it, and passing it to [TestCoroutineScope]
 * will not lead to it re-linking.
 */
public fun TestExceptionHandler(
    linkedScope: TestCoroutineScope? = null,
    handler: TestCoroutineScope.(CoroutineContext, Throwable) -> Unit
): CoroutineExceptionHandler = TestExceptionHandlerContextElement(handler, linkedScope)

/** The [CoroutineExceptionHandler] corresponding to the given [handler]. */
internal class TestExceptionHandlerContextElement(
    private val handler: TestCoroutineScope.(CoroutineContext, Throwable) -> Unit,
    private var testCoroutineScope: TestCoroutineScope?
): AbstractCoroutineContextElement(CoroutineExceptionHandler), CoroutineExceptionHandler
{
    private val lock = SynchronizedObject()

    /**
     * Links a [TestCoroutineScope] to this, unless there's already one linked.
     */
    fun tryRegisterTestCoroutineScope(scope: TestCoroutineScope): Boolean =
        synchronized(lock) {
            if (testCoroutineScope != null) {
                false
            } else {
                testCoroutineScope = scope
                true
            }
        }

    override fun handleException(context: CoroutineContext, exception: Throwable) {
        synchronized(lock) {
            testCoroutineScope
                ?: throw RuntimeException("Attempting to handle an exception using a `TestExceptionHandler` that is not linked to a `TestCoroutineScope`")
        }.handler(context, exception)
        /** it's okay if [handler] throws: [handleCoroutineException] deals with this. */
    }
}