/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.log4j

import kotlinx.coroutines.*
import org.apache.logging.log4j.ThreadContext
import org.junit.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class Log4jDiagnosticContextTest : TestBase() {

    @Before
    @After
    fun clearThreadContext() {
        ThreadContext.clearAll()
    }

    @Test
    fun testContextIsNotPassedByDefaultBetweenCoroutines() = runTest {
        expect(1)
        ThreadContext.put("myKey", "myValue")
        // Standalone launch
        GlobalScope.launch {
            assertEquals(null, ThreadContext.get("myKey"))
            expect(2)
        }.join()
        finish(3)
    }

    @Test
    fun testImmutableContextContainsOriginalContent() = runTest {
        expect(1)
        ThreadContext.put("myKey", "myValue")
        // Standalone launch
        GlobalScope.launch(immutableDiagnosticContext()) {
            assertEquals("myValue", ThreadContext.get("myKey"))
            expect(2)
        }.join()
        finish(3)
    }

    @Test
    fun testMutableContextContainsOriginalContent() = runTest {
        expect(1)
        ThreadContext.put("myKey", "myValue")
        // Standalone launch
        GlobalScope.launch(MutableDiagnosticContext()) {
            assertEquals("myValue", ThreadContext.get("myKey"))
            expect(2)
        }.join()
        finish(3)
    }

    @Test
    fun testContextInheritance() = runTest {
        expect(1)
        withContext(MutableDiagnosticContext()
            .put("myKey", "myValue")
        ) {
            // Update the global ThreadContext. This isn't tied to the CoroutineContext though, so shouldn't get used.
            ThreadContext.put("myKey", "myValue2")
            // Scoped launch with inherited Log4JThreadContext element
            launch(Dispatchers.Default) {
                assertEquals("myValue", ThreadContext.get("myKey"))
                expect(2)
            }.join()

            finish(3)
        }
        assertEquals("myValue", ThreadContext.get("myKey"))
    }

    @Test
    fun testContextPassedWhileOnSameThread() {
        ThreadContext.put("myKey", "myValue")
        // No ThreadContext element
        runBlocking {
            assertEquals("myValue", ThreadContext.get("myKey"))
        }
    }

    @Test
    fun testImmutableContextMayBeEmpty() {
        runBlocking(immutableDiagnosticContext()) {
            assertEquals(null, ThreadContext.get("myKey"))
        }
    }

    @Test
    fun testContextMayBeEmpty() {
        runBlocking(MutableDiagnosticContext()) {
            assertEquals(null, ThreadContext.get("myKey"))
        }
    }

    @Test
    fun testCoroutineContextWithLoggingContext() = runTest {
        val mainDispatcher = kotlin.coroutines.coroutineContext[ContinuationInterceptor]!!
        withContext(Dispatchers.Default
            + MutableDiagnosticContext().put("myKey", "myValue")
        ) {
            assertEquals("myValue", ThreadContext.get("myKey"))
            withContext(mainDispatcher) {
                assertEquals("myValue", ThreadContext.get("myKey"))
            }
        }
    }

    @Test
    fun testNestedContexts() {
        runBlocking(MutableDiagnosticContext().put("key", "value")) {
            withContext(MutableDiagnosticContext().put("key", "value2")){
                assertEquals("value2", ThreadContext.get("key"))
            }
            assertEquals("value", ThreadContext.get("key"))
        }
    }

    @Test
    fun testAcceptsNullValues() {
        runBlocking(MutableDiagnosticContext().put("key", null)) {
            assertNull(ThreadContext.get("key"))
        }
    }
}