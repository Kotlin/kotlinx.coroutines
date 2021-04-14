/*
 * Copyright 2016-2020 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

@UseExperimental(ExperimentalStdlibApi::class)
class DispatcherKeyTest : TestBase() {

    companion object CustomInterceptor : AbstractCoroutineContextElement(ContinuationInterceptor),
        ContinuationInterceptor {
        override fun <T> interceptContinuation(continuation: Continuation<T>): Continuation<T> {
            return continuation
        }
    }

    private val name = CoroutineName("test")

    @Test
    fun testDispatcher() {
        val context = name + CustomInterceptor
        assertNull(context[CoroutineDispatcher])
        assertSame(CustomInterceptor, context[ContinuationInterceptor])

        val updated = context + Dispatchers.Main
        val result: CoroutineDispatcher? = updated[CoroutineDispatcher]
        assertSame(Dispatchers.Main, result)
        assertSame(Dispatchers.Main, updated[ContinuationInterceptor])
        assertEquals(name, updated.minusKey(CoroutineDispatcher))
        assertEquals(name, updated.minusKey(ContinuationInterceptor))
    }

    @Test
    fun testExecutorCoroutineDispatcher() {
        val context = name + CustomInterceptor
        assertNull(context[ExecutorCoroutineDispatcher])
        val updated = context + Dispatchers.Main
        assertNull(updated[ExecutorCoroutineDispatcher])
        val executor = Dispatchers.Default
        val updated2 = updated + executor
        assertSame(Dispatchers.Default, updated2[ContinuationInterceptor])
        assertSame(Dispatchers.Default, updated2[CoroutineDispatcher])
        assertSame(Dispatchers.Default as ExecutorCoroutineDispatcher, updated2[ExecutorCoroutineDispatcher])
        assertEquals(name, updated2.minusKey(ContinuationInterceptor))
        assertEquals(name, updated2.minusKey(CoroutineDispatcher))
        assertEquals(name, updated2.minusKey(ExecutorCoroutineDispatcher))
    }
}
