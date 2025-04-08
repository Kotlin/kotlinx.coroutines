package kotlinx.coroutines

import kotlinx.coroutines.testing.*
import kotlinx.coroutines.internal.*
import kotlin.coroutines.*
import kotlin.test.*

class ThreadContextOrderTest : TestBase() {
    /*
     * The test verifies that two thread context elements are correctly nested:
     * The restoration order is the reverse of update order.
     */
    private val transactionalContext = commonThreadLocal<String>(Symbol("ThreadContextOrderTest#transactionalContext"))
    private val loggingContext = commonThreadLocal<String>(Symbol("ThreadContextOrderTest#loggingContext"))

    private val transactionalElement = object : ThreadContextElement<String> {
        override val key = CommonThreadLocalKey(transactionalContext)

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
        override val key = CommonThreadLocalKey(loggingContext)

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
