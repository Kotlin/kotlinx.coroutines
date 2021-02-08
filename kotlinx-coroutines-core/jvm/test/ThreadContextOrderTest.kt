/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import kotlinx.coroutines.internal.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class ThreadContextOrderTest : TestBase() {
    /*
     * The test verifies that two thread context elements are correctly nested:
     * The restoration order is the reverse of update order.
     */
    private val transactionalContext = ThreadLocal<String>()
    private val loggingContext = ThreadLocal<String>()

    private val transactionalElement = object : ThreadContextElement<String> {
        override val key = ThreadLocalKey(transactionalContext)

        override fun updateThreadContext(context: CoroutineContext): String {
            assertEquals("test", loggingContext.get())
            val previous = transactionalContext.get()
            transactionalContext.set("tr coroutine")
            return previous
        }

        override fun restoreThreadContext(context: CoroutineContext, oldState: String) {
            assertEquals("test", loggingContext.get())
            assertEquals("tr coroutine", transactionalContext.get())
            transactionalContext.set(oldState)
        }
    }

    private val loggingElement = object : ThreadContextElement<String> {
        override val key = ThreadLocalKey(loggingContext)

        override fun updateThreadContext(context: CoroutineContext): String {
            val previous = loggingContext.get()
            loggingContext.set("log coroutine")
            return previous
        }

        override fun restoreThreadContext(context: CoroutineContext, oldState: String) {
            assertEquals("log coroutine", loggingContext.get())
            assertEquals("tr coroutine", transactionalContext.get())
            loggingContext.set(oldState)
        }
    }

    @Test
    fun testCorrectOrder() = runTest {
        transactionalContext.set("test")
        loggingContext.set("test")
        launch(transactionalElement + loggingElement) {
            assertEquals("log coroutine", loggingContext.get())
            assertEquals("tr coroutine", transactionalContext.get())
        }
        assertEquals("test", loggingContext.get())
        assertEquals("test", transactionalContext.get())

    }
}
