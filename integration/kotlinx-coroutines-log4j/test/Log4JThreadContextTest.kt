/*
 * Copyright 2016-2018 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.log4j

import kotlinx.coroutines.*
import org.apache.logging.log4j.CloseableThreadContext
import org.apache.logging.log4j.ThreadContext
import org.junit.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class Log4JThreadContextTest : TestBase() {
    @Before
    fun setUp() {
        ThreadContext.clearAll()
    }

    @After
    fun tearDown() {
        ThreadContext.clearAll()
    }

    @Test
    fun testContextIsNotPassedByDefaultBetweenCoroutines() = runTest {
        expect(1)
        ThreadContext.put("myKey", "myValue")
        ThreadContext.push("stack1")
        // Standalone launch
        GlobalScope.launch {
            assertEquals(null, ThreadContext.get("myKey"))
            assertEquals("", ThreadContext.peek())
            expect(2)
        }.join()
        finish(3)
    }

    @Test
    fun testContextCanBePassedBetweenCoroutines() = runTest {
        expect(1)
        ThreadContext.put("myKey", "myValue")
        ThreadContext.push("stack1")
        // Scoped launch with Log4JThreadContext element
        launch(Log4JThreadContext()) {
            assertEquals("myValue", ThreadContext.get("myKey"))
            assertEquals("stack1", ThreadContext.peek())
            expect(2)
        }.join()

        finish(3)
    }

    @Test
    fun testContextInheritance() = runTest {
        expect(1)
        ThreadContext.put("myKey", "myValue")
        ThreadContext.push("stack1")
        withContext(Log4JThreadContext()) {
            ThreadContext.put("myKey", "myValue2")
            ThreadContext.push("stack2")
            // Scoped launch with inherited Log4JThreadContext element
            launch(Dispatchers.Default) {
                assertEquals("myValue", ThreadContext.get("myKey"))
                assertEquals("stack1", ThreadContext.peek())
                expect(2)
            }.join()

            finish(3)
        }
        assertEquals("myValue", ThreadContext.get("myKey"))
        assertEquals("stack1", ThreadContext.peek())
    }

    @Test
    fun testContextPassedWhileOnMainThread() {
        ThreadContext.put("myKey", "myValue")
        ThreadContext.push("stack1")
        // No ThreadContext element
        runBlocking {
            assertEquals("myValue", ThreadContext.get("myKey"))
            assertEquals("stack1", ThreadContext.peek())
        }
    }

    @Test
    fun testContextCanBePassedWhileOnMainThread() {
        ThreadContext.put("myKey", "myValue")
        ThreadContext.push("stack1")
        runBlocking(Log4JThreadContext()) {
            assertEquals("myValue", ThreadContext.get("myKey"))
            assertEquals("stack1", ThreadContext.peek())
        }
    }

    @Test
    fun testContextNeededWithOtherContext() {
        ThreadContext.put("myKey", "myValue")
        ThreadContext.push("stack1")
        runBlocking(Log4JThreadContext()) {
            assertEquals("myValue", ThreadContext.get("myKey"))
            assertEquals("stack1", ThreadContext.peek())
        }
    }

    @Test
    fun testContextMayBeEmpty() {
        runBlocking(Log4JThreadContext()) {
            assertEquals(null, ThreadContext.get("myKey"))
            assertEquals("", ThreadContext.peek())
        }
    }

    @Test
    fun testContextWithContext() = runTest {
        ThreadContext.put("myKey", "myValue")
        ThreadContext.push("stack1")
        val mainDispatcher = kotlin.coroutines.coroutineContext[ContinuationInterceptor]!!
        withContext(Dispatchers.Default + Log4JThreadContext()) {
            assertEquals("myValue", ThreadContext.get("myKey"))
            assertEquals("stack1", ThreadContext.peek())
            withContext(mainDispatcher) {
                assertEquals("myValue", ThreadContext.get("myKey"))
                assertEquals("stack1", ThreadContext.peek())
            }
        }
    }
}