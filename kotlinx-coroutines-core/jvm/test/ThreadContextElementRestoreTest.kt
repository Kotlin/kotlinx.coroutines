/*
 * Copyright 2016-2019 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines

import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class ThreadContextElementRestoreTest : TestBase() {
    private val tl = ThreadLocal<String?>()

    // Checks that ThreadLocal context is properly restored after executing the given block inside
    // withContext(tl.asContextElement("OK")) code running in different outer contexts
    private inline fun check(crossinline block: suspend () -> Unit) = runTest {
        val mainDispatcher = coroutineContext[ContinuationInterceptor] as CoroutineDispatcher
        // Scenario #1: withContext(ThreadLocal) direct from runTest
        withContext(tl.asContextElement("OK")) {
            block()
            assertEquals("OK", tl.get())
        }
        assertEquals(null, tl.get())
        // Scenario #2: withContext(ThreadLocal) from coroutineScope
        coroutineScope {
            withContext(tl.asContextElement("OK")) {
                block()
                assertEquals("OK", tl.get())
            }
            assertEquals(null, tl.get())
        }
        // Scenario #3: withContext(ThreadLocal) from undispatched withContext
        withContext(CoroutineName("NAME")) {
            withContext(tl.asContextElement("OK")) {
                block()
                assertEquals("OK", tl.get())
            }
            assertEquals(null, tl.get())
        }
        // Scenario #4: withContext(ThreadLocal) from dispatched withContext
        withContext(wrapperDispatcher()) {
            withContext(tl.asContextElement("OK")) {
                block()
                assertEquals("OK", tl.get())
            }
            assertEquals(null, tl.get())
        }
        // Scenario #5: withContext(ThreadLocal) from withContext(ThreadLocal)
        withContext(tl.asContextElement(null)) {
            withContext(tl.asContextElement("OK")) {
                block()
                assertEquals("OK", tl.get())
            }
            assertEquals(null, tl.get())
        }
        // Scenario #6: withContext(ThreadLocal) from withTimeout
        withTimeout(1000) {
            withContext(tl.asContextElement("OK")) {
                block()
                assertEquals("OK", tl.get())
            }
            assertEquals(null, tl.get())
        }
        // Scenario #7: withContext(ThreadLocal) from withContext(Unconfined)
        withContext(Dispatchers.Unconfined) {
            withContext(tl.asContextElement("OK")) {
                block()
                assertEquals("OK", tl.get())
            }
            assertEquals(null, tl.get())
        }
        // Scenario #8: withContext(ThreadLocal) from withContext(Default)
        withContext(Dispatchers.Default) {
            withContext(tl.asContextElement("OK")) {
                block()
                assertEquals("OK", tl.get())
            }
            assertEquals(null, tl.get())
        }
        // Scenario #9: withContext(ThreadLocal) from withContext(mainDispatcher)
        withContext(mainDispatcher) {
            withContext(tl.asContextElement("OK")) {
                block()
                assertEquals("OK", tl.get())
            }
            assertEquals(null, tl.get())
        }
    }

    @Test
    fun testSimpleNoSuspend() =
        check {}

    @Test
    fun testSimpleDelay() = check {
        delay(1)
    }

    @Test
    fun testSimpleYield() = check {
        yield()
    }

    private suspend fun deepDelay() {
        deepDelay2(); deepDelay2()
    }

    private suspend fun deepDelay2() {
        delay(1); delay(1)
    }

    @Test
    fun testDeepDelay() = check {
        deepDelay()
    }

    private suspend fun deepYield() {
        deepYield2(); deepYield2()
    }

    private suspend fun deepYield2() {
        yield(); yield()
    }

    @Test
    fun testDeepYield() = check {
        deepYield()
    }

    @Test
    fun testCoroutineScopeDelay() = check {
        coroutineScope {
            delay(1)
        }
    }

    @Test
    fun testCoroutineScopeYield() = check {
        coroutineScope {
            yield()
        }
    }

    @Test
    fun testWithContextUndispatchedDelay() = check {
        withContext(CoroutineName("INNER")) {
            delay(1)
        }
    }

    @Test
    fun testWithContextUndispatchedYield() = check {
        withContext(CoroutineName("INNER")) {
            yield()
        }
    }

    @Test
    fun testWithContextDispatchedDelay() = check {
        withContext(wrapperDispatcher()) {
            delay(1)
        }
    }

    @Test
    fun testWithContextDispatchedYield() = check {
        withContext(wrapperDispatcher()) {
            yield()
        }
    }

    @Test
    fun testWithTimeoutDelay() = check {
        withTimeout(1000) {
            delay(1)
        }
    }

    @Test
    fun testWithTimeoutYield() = check {
        withTimeout(1000) {
            yield()
        }
    }

    @Test
    fun testWithUnconfinedContextDelay() = check {
        withContext(Dispatchers.Unconfined) {
            delay(1)
        }
    }
    @Test
    fun testWithUnconfinedContextYield() = check {
        withContext(Dispatchers.Unconfined) {
            yield()
        }
    }
}
