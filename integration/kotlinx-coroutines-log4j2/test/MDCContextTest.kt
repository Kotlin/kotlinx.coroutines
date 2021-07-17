/*
 * Copyright 2016-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license.
 */

package kotlinx.coroutines.log4j2

import kotlinx.coroutines.*
import org.apache.logging.log4j.ThreadContext
import org.junit.*
import org.junit.Test
import kotlin.coroutines.*
import kotlin.test.*

class MDCContextTest : TestBase() {
    @Before
    fun setUp() {
        ThreadContext.clearMap()
    }

    @After
    fun tearDown() {
        ThreadContext.clearMap()
    }

    @Test
    fun testContextIsNotPassedByDefaultBetweenCoroutines() = runTest {
        expect(1)
        ThreadContext.put("myKey", "myValue")
        // Standalone launch
        GlobalScope.launch {
            assertNull(ThreadContext.get("myKey"))
            expect(2)
        }.join()
        finish(3)
    }

    @Test
    fun testContextCanBePassedBetweenCoroutines() = runTest {
        expect(1)
        ThreadContext.put("myKey", "myValue")
        // Scoped launch with MDCContext element
        launch(MDCContext()) {
            assertEquals("myValue", ThreadContext.get("myKey"))
            expect(2)
        }.join()

        finish(3)
    }

    @Test
    fun testContextInheritance() = runTest {
        expect(1)
        ThreadContext.put("myKey", "myValue")
        withContext(MDCContext()) {
            ThreadContext.put("myKey", "myValue2")
            // Scoped launch with inherited MDCContext element
            launch(Dispatchers.Default) {
                assertEquals("myValue", ThreadContext.get("myKey"))
                expect(2)
            }.join()

            finish(3)
        }
        assertEquals("myValue", ThreadContext.get("myKey"))
    }

    @Test
    fun testContextPassedWhileOnMainThread() {
        ThreadContext.put("myKey", "myValue")
        // No MDCContext element
        runBlocking {
            assertEquals("myValue", ThreadContext.get("myKey"))
        }
    }

    @Test
    fun testContextCanBePassedWhileOnMainThread() {
        ThreadContext.put("myKey", "myValue")
        runBlocking(MDCContext()) {
            assertEquals("myValue", ThreadContext.get("myKey"))
        }
    }

    @Test
    fun testContextNeededWithOtherContext() {
        ThreadContext.put("myKey", "myValue")
        runBlocking(MDCContext()) {
            assertEquals("myValue", ThreadContext.get("myKey"))
        }
    }

    @Test
    fun testContextMayBeEmpty() {
        runBlocking(MDCContext()) {
            assertNull(ThreadContext.get("myKey"))
        }
    }

    @Test
    fun testContextWithContext() = runTest {
        ThreadContext.put("myKey", "myValue")
        val mainDispatcher = kotlin.coroutines.coroutineContext[ContinuationInterceptor]!!
        withContext(Dispatchers.Default + MDCContext()) {
            assertEquals("myValue", ThreadContext.get("myKey"))
            withContext(mainDispatcher) {
                assertEquals("myValue", ThreadContext.get("myKey"))
            }
        }
    }
}
